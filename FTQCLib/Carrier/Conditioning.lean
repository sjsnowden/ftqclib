/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.PrecisionGauge
import FTQCLib.Carrier.ZModTwo
import FTQCLib.Carrier.BoundElimination
import FTQCLib.Aut.Defs

/-!
# Conditioning a carrier state on a Pauli, the outcome bit, and free-bit bookkeeping

Measuring a Pauli `P` with outcome `b` is, on amplitude functions, the spectral projection
`Π_b f = ½(f + (−1)^b · P f)` (`docs/GLOSSARY.md`, section 5; decision D5 names it the referee of
conditioning). The Pauli carries its sign: `SignedPauli` is `(−1)^sign` times a Hermitian Pauli
acting by `pauliAct`, `(P f)(w) = i^{yWeight P}·(−1)^{Z·(w + X)}·f(w + X)`, so every Hermitian
Pauli with either sign is one value of the type. `pauliProjection P b` is the referee. Carrier
states are not renormalised (D3), and an outcome that cannot occur gives the zero function, which
is a `KernelSumState` and not a carrier (D10).

**Conditioning has H's shape** (`docs/TARGETS.md`, T10; `docs/STEPS.md`, entry 2026-09-29l). The
projection is `½ Σ_{t ∈ 𝔽₂} ((−1)^b P)^t f`, a sum over one new bit `t`. Which of the two
constructors carries it is decided by one test, whether `P`'s X-part `a` lies in the support's
directions, the shadow `π_X(L)`:

* **`a ∈ π_X(L)`: one new bound bit** (`conditionBound`, the shape of H's free rule
  `applyHFiner`). Both `w` and `w + a` lie on the support together, so `t` becomes a new bound
  bit: the exponent is `Q(w ⊕ t·a, y) + t·φ(w)`, where `φ` is the exponent of the factor
  `(−1)^b·(−1)^sign·i^{yWeight}·(−1)^{Z·(w+a)}` (`branchPhase`), and the scale is `c/√2`: the
  `½` of the projection is `1/√2` from the scale and `1/√2` from the height's normalisation. The
  support is unchanged.
* **`a ∉ π_X(L)`: no new bound bit, and a larger support** (`conditionRaise`, the shape of H's
  raise `hRaise`). The two halves `f` and `P f` live on the disjoint cosets `x₀ + π_X(L)` and
  `x₀ + a + π_X(L)`, so the support grows to their union, `t` is the affine function
  `t(w) = u·(w + x₀)` that tells the two cosets apart (`u` vanishes on `π_X(L)` and has
  `u·a = 1`: `Separates`), the exponent is `Q(w ⊕ t(w)·a, y) + t(w)·φ(w)`, and the scale is `c/2`.
  The Lagrangian becomes `(L ∩ P^⊥) + ⟨P⟩`, `pauliCondition`'s formula off `L`; its shadow is
  `π_X(L) + ⟨a⟩` when `L` is co-isotropic, which is the hypothesis of the amplitude theorems.

`condition` applies the one constructor the test chooses. Each constructor's amplitude is the
projection, at any height, for every Pauli with its sign (`condition_cover`, `amp_condition`).
For `P = Z_j` the X-part is `0`, always in the shadow: conditioning adds one bound bit whose
difference is the half turn times `w_j + b`, which is the shape a collapse removes
(`elimCollapse`), cutting the support to `w_j = b` whether bit `j` is free or determined by the
others; the referee's side of this is `pauliProjection_zPauli_single`, and an impossible outcome
gives amplitude zero.

**Precision.** The factor `(−1)^b` needs precision at least one and `i^{yWeight P}` at least two
when `P` has an odd number of Y. Both constructors first lift the exponent by the gauge rewrite R7
(`FTQCLib.Hilbert.liftTo`, `PrecisionGauge.lean`) to `conditionPrecision S.m P`, which is `S.m`
itself on a carrier state unless `P` has an odd number of Y and `S.m = 1`. So the amplitude
theorems carry no hypothesis on the precision.

**The outcome as a free bit** (D2 as revised). `conditionOutcome S P` is the one carrier state
`Σ_b ∣b⟩ ⊗ Π_b f` on one more free bit, the last: its amplitude at `(w, b)` is `(Π_b f)(w)`
(`amp_conditionOutcome`), and evaluating the last free bit at `b` gives `condition S P b`
(`conditionOutcome_eval`). It is `condition` itself, applied to the input with a new last free bit
on which the amplitude does not depend (`appendFreeBit`) and to `P ⊗ Z` (`SignedPauli.appendZ`),
since `½(1 + P ⊗ Z)` is `Π_b` on the fibre of `b`; so it is the same cover, with the same test.

**Free-bit bookkeeping.** `permuteFreeBits σ` relabels the free bits: input bit `j` becomes output
bit `σ j` (`amp_permuteFreeBits`). `dropFreeBit j` removes a free bit that the support determines,
a constant or an affine function of the other free bits, by substituting that function for it
in the exponent (the XOR form `xorForm`, exact at every precision). The support determines bit `j`
exactly when `e_j ∉ π_X(L)`, the hypothesis of every theorem about it: no two words of the support
coset then differ only at `j`. Its amplitude at `w` is the input's at the one extension of `w`
on the support, written as the sum over both extensions, at most one of which is on the support
(`amp_dropFreeBit`); it keeps the carrier property (`isCarrier_dropFreeBit`). On a free bit that
the support does not determine, `dropFreeBit` is defined and nothing is claimed of it.

Everything here is frame-pure. No `FTQCLib.Hilbert` module is imported; `liftTo` keeps its full
name `FTQCLib.Hilbert.liftTo` from before its move.

## Main definitions

* `SignedPauli`, `SignedPauli.act` — a Pauli with its sign, and its action on amplitude functions.
* `pauliProjection` — the referee `Π_b f = ½(f + (−1)^b · P f)`.
* `conditionPrecision`, `iPowExp`, `branchPhase`, `shiftSubst` — the precision, the exponent of the
  factor on the shifted branch, and the shift `w ↦ w ⊕ t·a` of the free block.
* `conditionBound`, `conditionRaise`, `Separates`, `condition` — the two constructors, the data of
  the second, and conditioning, which applies the one the test chooses.
* `appendFreeBit`, `SignedPauli.appendZ`, `conditionOutcome` — the outcome as a new last free bit.
* `permuteFreeBits` — a relabelling of the free bits.
* `ReadsBit`, `dropFreeBitBy`, `dropFreeBit` — dropping a free bit the support determines.

## Main results

* `condition_cover` — **the cover**: the test `P.X ∈ π_X(L)` chooses exactly one constructor, and
  that constructor's amplitude is the projection.
* `amp_condition` — conditioning's amplitude is `½(S + (−1)^b · P S)`, at any height.
* `amp_conditionOutcome`, `conditionOutcome_eval` — the outcome-bit form and its evaluations.
* `amp_permuteFreeBits` — relabelling the free bits precomposes the amplitude.
* `amp_dropFreeBit`, `isCarrier_dropFreeBit` — dropping a determined free bit.
* `charOf_iPowExp`, `pauliProjection_zPauli_single` — the constant `i^e`, and the referee at `Z_j`.
* `isCarrier_conditionOutcome` — the outcome-bit form of a carrier state is a carrier state, from
  `condition_L` (conditioning keeps an isotropic, co-isotropic Lagrangian: `isStabilizer_raise`,
  `orthogonal_raise_le`), `isStabilizer_appendFreeBit` and `amp_conditionOutcome_ne_zero`.
* `conditionOutcome_m`, `conditionPrecision_eq`, `yWeight_appendZ`, `pauliProjection_zero_add_one`
  — the outcome-bit form's precision, and the two projections adding up to the function.

## Implementation notes

* The seven theorems `condition_cover`, `amp_condition`, `amp_conditionOutcome`,
  `conditionOutcome_eval`, `amp_permuteFreeBits`, `amp_dropFreeBit` and `isCarrier_dropFreeBit`
  are stated here and proved at T10.3.1, T10.3.2 and T10.3.3 (`docs/STEPS.md`, phase 2).
* The carrier lemmas of the outcome-bit form (`isCarrier_conditionOutcome` and the eight it
  rests on) were proved at T14.3.1 as private helpers of `Protocol.lean` and moved here, public,
  for the protocols of T15 and T16 (`docs/STEPS.md`, entry 2026-10-01e).
* The amplitude theorems of conditioning take co-isotropy of `L` and nothing else. The bound
  constructor needs no hypothesis; the raise constructor needs co-isotropy for its support: a
  Z-type element of `L^⊥` that anticommutes with `P` keeps the shadow of `L ∩ P^⊥` equal to
  `π_X(L)`. Without it the shadow can shrink (`L = ⟨Y₀Z₁⟩`, `P = X₁`).
* `condition` and `dropFreeBit` choose their data (a separator, a reader) by `Classical.epsilon`,
  so they are total and carry no proof; the theorems name the data they need through the test.
* The sum `Z·(w + a)` in `branchPhase` is the ordinary sum of the bits: it is read only under the
  top bit `2^{k−1}`, where the carries vanish (`two_pow_mul_xorForm`'s argument). The shift
  `w ⊕ t·a` and the selector `t(w)` are substituted into the exponent and multiplied by `i^e`, so
  they use the exact XOR forms `polyXor` and `xorForm`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## A Pauli with its sign, and the referee -/

/-- A Pauli with its sign: `(−1)^sign` times the Hermitian Pauli `pauli`, which acts by
`pauliAct`. Every Hermitian element of the Pauli group is one value. -/
@[ext]
structure SignedPauli (n : ℕ) where
  /-- The sign, as the exponent of `−1`. -/
  sign : ZMod 2
  /-- The Hermitian Pauli, acting by `pauliAct`. -/
  pauli : Pauli n

/-- The action of a Pauli with its sign on an amplitude function:
`(−1)^sign · i^{yWeight}·(−1)^{Z·(w + X)}·f(w + X)`. -/
noncomputable def SignedPauli.act (P : SignedPauli n) (f : (Fin n → ZMod 2) → ℂ) :
    (Fin n → ZMod 2) → ℂ :=
  fun w => (-1 : ℂ) ^ P.sign.val * pauliAct P.pauli f w

/-- **The referee of conditioning** (D5): the spectral projection
`Π_b f = ½(f + (−1)^b · P f)` onto the `(−1)^b`-eigenspace of the Pauli `P` with its sign. -/
noncomputable def pauliProjection (P : SignedPauli n) (b : ZMod 2) (f : (Fin n → ZMod 2) → ℂ) :
    (Fin n → ZMod 2) → ℂ :=
  fun w => (1 / 2 : ℂ) * (f w + (-1 : ℂ) ^ b.val * P.act f w)

/-! ## The precision and the branch's phase -/

/-- The precision conditioning works at: the input's precision `m`, raised to `1` for the sign
`−1` and to `2` when `P` has an odd number of Y, for its factor `i^{yWeight}`. On a carrier state
(`1 ≤ m`) it is `m` unless `P` has an odd number of Y and `m = 1`. -/
def conditionPrecision (m : ℕ) (P : SignedPauli n) : ℕ :=
  if yWeight P.pauli % 2 = 0 then max m 1 else max m 2

/-- The input's precision is at most the conditioning precision: the lift is R7. -/
theorem le_conditionPrecision (m : ℕ) (P : SignedPauli n) : m ≤ conditionPrecision m P := by
  unfold conditionPrecision
  split
  · exact le_max_left m 1
  · exact le_max_left m 2

/-- The conditioning precision is positive: the sign `−1` is representable. -/
theorem one_le_conditionPrecision (m : ℕ) (P : SignedPauli n) : 1 ≤ conditionPrecision m P := by
  unfold conditionPrecision
  split
  · exact le_max_right m 1
  · exact le_trans (by norm_num) (le_max_right m 2)

/-- With an odd number of Y the conditioning precision is at least two: `i` is representable. -/
theorem two_le_conditionPrecision {m : ℕ} {P : SignedPauli n} (hodd : yWeight P.pauli % 2 = 1) :
    2 ≤ conditionPrecision m P := by
  unfold conditionPrecision
  rw [if_neg (by omega)]
  exact le_max_right m 2

/-- The exponent of `i^e` at precision `k`: `2^{k−1}·⌊e/2⌋ + 2^{k−2}·(e mod 2)`. Its character
is `i^e` at `1 ≤ k` when `e` is even or `2 ≤ k` (`charOf_iPowExp`); `conditionPrecision` is such
a `k` for `e = yWeight P`. -/
def iPowExp (k e : ℕ) : ZMod (2 ^ k) :=
  (2 : ZMod (2 ^ k)) ^ (k - 1) * ((e / 2 : ℕ) : ZMod (2 ^ k))
    + (2 : ZMod (2 ^ k)) ^ (k - 2) * ((e % 2 : ℕ) : ZMod (2 ^ k))

/-- The character of `iPowExp k e` is `i^e`, at `1 ≤ k` when `e` is even and at `2 ≤ k`. -/
theorem charOf_iPowExp {k : ℕ} (e : ℕ) (hk : 1 ≤ k) (hodd : e % 2 = 1 → 2 ≤ k) :
    charOf k (iPowExp k e) = Complex.I ^ e := by
  have hlow : charOf k ((2 : ZMod (2 ^ k)) ^ (k - 2) * ((e % 2 : ℕ) : ZMod (2 ^ k)))
      = Complex.I ^ (e % 2) := by
    rcases Nat.mod_two_eq_zero_or_one e with h | h
    · rw [h, Nat.cast_zero, mul_zero, charOf_zero, pow_zero]
    · exact charOf_two_pow_sub_two_mul (hodd h) (e % 2)
  unfold iPowExp
  rw [charOf_add, charOf_two_pow_mul hk, hlow, neg_one_pow_eq_I_pow, ← pow_add, Nat.div_add_mod]

/-- The exponent, at precision `k`, of the factor that `(−1)^b P` puts on its shifted branch:
`(−1)^{b + sign}·i^{yWeight}·(−1)^{Z·(w + X)}`, as a polynomial in the free word, whose variable
`j` is read at `ι j`. The sum `Z·(w + X)` is the ordinary sum of the bits, read only under the
top bit `2^{k−1}`. -/
noncomputable def branchPhase {N : ℕ} (k : ℕ) (ι : Fin n → Fin N) (P : SignedPauli n)
    (b : ZMod 2) : DiagPhase N k :=
  MvPolynomial.C ((2 : ZMod (2 ^ k)) ^ (k - 1))
      * (MvPolynomial.C (((b + P.sign).val : ZMod (2 ^ k)))
        + ∑ j : Fin n, MvPolynomial.C (((P.pauli.Z j).val : ZMod (2 ^ k)))
            * (MvPolynomial.X (ι j) + MvPolynomial.C (((P.pauli.X j).val : ZMod (2 ^ k)))))
    + MvPolynomial.C (iPowExp k (yWeight P.pauli))

/-- The shift `w ↦ w ⊕ t·a` of the free block, where `t` is the bit the polynomial `T` evaluates
to: a free variable `j` with `a j = 1` becomes `X_j ⊕ T` (`polyXor`, exact at every precision);
every variable is renamed by `ι`. -/
noncomputable def shiftSubst {N h k : ℕ} (ι : Fin (n + h) → Fin N) (a : Fin n → ZMod 2)
    (T : DiagPhase N k) (Q : DiagPhase (n + h) k) : DiagPhase N k :=
  MvPolynomial.bind₁
    (fun l : Fin (n + h) =>
      if Fin.append a (0 : Fin h → ZMod 2) l = 1 then polyXor (MvPolynomial.X (ι l)) T
      else MvPolynomial.X (ι l))
    Q

/-! ## The two constructors -/

/-- **One new bound bit** (the shape of H's free rule). For `P`'s X-part in the shadow: the new
last bound bit `t` shifts the free word by `t·a` and carries the branch's phase, the exponent is
lifted to `conditionPrecision`, the scale is `c/√2`, and the support is unchanged. -/
noncomputable def conditionBound (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2) :
    KernelSumState n where
  m := conditionPrecision S.m P
  h := S.h + 1
  Q := shiftSubst Fin.castSucc P.pauli.X (MvPolynomial.X (Fin.last (n + S.h)))
        (FTQCLib.Hilbert.liftTo (conditionPrecision S.m P) (le_conditionPrecision S.m P) S.Q)
      + MvPolynomial.X (Fin.last (n + S.h))
        * branchPhase (conditionPrecision S.m P) (fun j => (Fin.castAdd S.h j).castSucc) P b
  c := S.c / (Real.sqrt 2 : ℂ)
  L := S.L
  x₀ := S.x₀

/-- **No new bound bit, and a larger support** (the shape of H's raise). For `P`'s X-part off the
shadow, with a separator `u`: the selector `t(w) = u·(w + x₀)` shifts the free word by `t(w)·a`
and carries the branch's phase, the exponent is lifted to `conditionPrecision`, the scale is `c/2`,
and the Lagrangian is `(L ∩ P^⊥) + ⟨P⟩`, whose shadow is `π_X(L) + ⟨a⟩` on a co-isotropic `L`. -/
noncomputable def conditionRaise (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2)
    (u : Fin n → ZMod 2) : KernelSumState n where
  m := conditionPrecision S.m P
  h := S.h
  Q := shiftSubst id P.pauli.X (xorForm (h := S.h) u (dotF2 u S.x₀))
        (FTQCLib.Hilbert.liftTo (conditionPrecision S.m P) (le_conditionPrecision S.m P) S.Q)
      + xorForm (h := S.h) u (dotF2 u S.x₀)
        * branchPhase (conditionPrecision S.m P) (Fin.castAdd S.h) P b
  c := S.c / 2
  L := (S.L ⊓ LinearMap.BilinForm.orthogonal omegaBilin (Submodule.span (ZMod 2) {P.pauli}))
      ⊔ Submodule.span (ZMod 2) {P.pauli}
  x₀ := S.x₀

/-- The bound constructor adds one bound bit. -/
@[simp] theorem conditionBound_h (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2) :
    (conditionBound S P b).h = S.h + 1 := rfl

/-- The bound constructor's scale is `c/√2`. -/
@[simp] theorem conditionBound_c (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2) :
    (conditionBound S P b).c = S.c / (Real.sqrt 2 : ℂ) := rfl

/-- The bound constructor keeps the Lagrangian. -/
@[simp] theorem conditionBound_L (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2) :
    (conditionBound S P b).L = S.L := rfl

/-- The raise constructor adds no bound bit. -/
@[simp] theorem conditionRaise_h (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2)
    (u : Fin n → ZMod 2) : (conditionRaise S P b u).h = S.h := rfl

/-- The raise constructor's scale is `c/2`. -/
@[simp] theorem conditionRaise_c (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2)
    (u : Fin n → ZMod 2) : (conditionRaise S P b u).c = S.c / 2 := rfl

open Classical in
/-- **Conditioning on a Pauli with its sign, at outcome `b`.** The test is whether `P`'s X-part
lies in the support's directions, the shadow `π_X(L)`: if it does, one new bound bit
(`conditionBound`); if not, no new bound bit and a larger support (`conditionRaise`, with a
separator chosen). -/
noncomputable def condition (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2) :
    KernelSumState n :=
  if P.pauli.X ∈ Submodule.map xProj S.L then conditionBound S P b
  else conditionRaise S P b (Classical.epsilon (Separates (Submodule.map xProj S.L) P.pauli.X))

/-- In the shadow, conditioning is the bound constructor. -/
theorem condition_of_mem {S : KernelSumState n} {P : SignedPauli n}
    (hP : P.pauli.X ∈ Submodule.map xProj S.L) (b : ZMod 2) :
    condition S P b = conditionBound S P b := by
  unfold condition
  exact if_pos hP

/-! ## The factor on the shifted branch, and the shift -/

/-- The character of the branch's phase is the factor `(−1)^b·(−1)^sign·i^{yWeight}·(−1)^{Z·(w+X)}`
that `(−1)^b P` puts on its shifted branch, where `w` is the free word read through `ι`. -/
theorem charOf_branchPhase_eval {N k : ℕ} (ι : Fin n → Fin N) (P : SignedPauli n)
    (b : ZMod 2) (hk : 1 ≤ k) (hodd : yWeight P.pauli % 2 = 1 → 2 ≤ k) (v : Fin N → ZMod 2) :
    charOf k ((branchPhase k ι P b).eval v)
      = (-1 : ℂ) ^ b.val * ((-1 : ℂ) ^ P.sign.val * (Complex.I ^ yWeight P.pauli
          * (-1 : ℂ) ^ zDot P.pauli ((fun j => v (ι j)) + P.pauli.X))) := by
  have hsum : DiagPhase.eval (MvPolynomial.C (((b + P.sign).val : ZMod (2 ^ k)))
        + ∑ j : Fin n, MvPolynomial.C (((P.pauli.Z j).val : ZMod (2 ^ k)))
            * (MvPolynomial.X (ι j) + MvPolynomial.C (((P.pauli.X j).val : ZMod (2 ^ k))))) v
      = (((b + P.sign).val + ∑ j : Fin n, (P.pauli.Z j).val * ((v (ι j)).val + (P.pauli.X j).val)
          : ℕ) : ZMod (2 ^ k)) := by
    simp only [DiagPhase.eval, map_add, map_sum, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, DiagPhase.liftBinary]
    push_cast
    rfl
  unfold branchPhase
  rw [DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_C, hsum,
    charOf_add, charOf_two_pow_mul hk, charOf_iPowExp _ hk hodd]
  have hpar : (((b + P.sign).val + ∑ j : Fin n, (P.pauli.Z j).val * ((v (ι j)).val
      + (P.pauli.X j).val) : ℕ) : ZMod 2)
      = ((b.val + P.sign.val + zDot P.pauli ((fun j => v (ι j)) + P.pauli.X) : ℕ) : ZMod 2) := by
    push_cast
    rw [zDot_cast_two]
    simp only [ZMod.natCast_val, ZMod.cast_id', id, Pi.add_apply]
  rw [neg_one_pow_eq_of_cast_eq hpar, pow_add, pow_add]
  ring

/-- The shift evaluates to the shifted word: where `T` evaluates to the bit `t`, `shiftSubst`
evaluates the exponent at `z ⊕ t·a`, read through `ι`. -/
theorem shiftSubst_eval {N h k : ℕ} (ι : Fin (n + h) → Fin N) (a : Fin n → ZMod 2)
    (T : DiagPhase N k) (Q : DiagPhase (n + h) k) (z : Fin N → ZMod 2) (t : ZMod 2)
    (hT : T.eval z = (t.val : ZMod (2 ^ k))) :
    (shiftSubst ι a T Q).eval z
      = Q.eval (fun l => z (ι l) + t * Fin.append a (0 : Fin h → ZMod 2) l) := by
  unfold shiftSubst DiagPhase.eval
  have hb := MvPolynomial.aeval_bind₁ (R := ZMod (2 ^ k)) (S := ZMod (2 ^ k))
    (DiagPhase.liftBinary z)
    (fun l : Fin (n + h) =>
      if Fin.append a (0 : Fin h → ZMod 2) l = 1 then polyXor (MvPolynomial.X (ι l)) T
      else MvPolynomial.X (ι l)) Q
  simp only [MvPolynomial.aeval_eq_eval] at hb
  rw [hb]
  congr 2
  funext l
  simp only [DiagPhase.liftBinary]
  split_ifs with hl
  · rw [← DiagPhase.eval, polyXor_eval, hT, DiagPhase.eval_X, hl, mul_one, val_add_val]
  · have hl0 : Fin.append a (0 : Fin h → ZMod 2) l = 0 :=
      (show ∀ x : ZMod 2, x ≠ 1 → x = 0 by decide) _ hl
    rw [hl0, mul_zero, add_zero, MvPolynomial.eval_X]
    rfl

/-- The factor `(−1)^b·(−1)^sign·i^{yWeight}·(−1)^{Z·(w+X)}` that `(−1)^b P` puts on the value at
`w + X`. -/
noncomputable def shiftFactor (P : SignedPauli n) (b : ZMod 2) (w : Fin n → ZMod 2) : ℂ :=
  (-1 : ℂ) ^ b.val * ((-1 : ℂ) ^ P.sign.val * (Complex.I ^ yWeight P.pauli
    * (-1 : ℂ) ^ zDot P.pauli (w + P.pauli.X)))

/-- The referee as the value at `w` plus the factor times the value at `w + X`, halved. -/
theorem pauliProjection_apply (P : SignedPauli n) (b : ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) (w : Fin n → ZMod 2) :
    pauliProjection P b f w = 1 / 2 * (f w + shiftFactor P b w * f (w + P.pauli.X)) := by
  unfold pauliProjection SignedPauli.act pauliAct shiftFactor
  ring

/-- Shifting the free block of an appended word by `t·a`. -/
theorem append_add_mul_append {h : ℕ} (w a : Fin n → ZMod 2) (y : Fin h → ZMod 2)
    (t : ZMod 2) :
    (fun l => Fin.append w y l + t * Fin.append a (0 : Fin h → ZMod 2) l)
      = Fin.append (w + t • a) y := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun j => ?_) l
  · simp only [Fin.append_left, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · simp only [Fin.append_right, Pi.zero_apply, mul_zero, add_zero]

/-- One summand of the bound constructor: the input's exponent at the word shifted by `t·a`, times
the `t`-th power of the factor. -/
private theorem charOf_conditionBound_term (S : KernelSumState n) (P : SignedPauli n)
    (b : ZMod 2) (w : Fin n → ZMod 2) (y : Fin S.h → ZMod 2) (t : ZMod 2) :
    charOf (conditionBound S P b).m
        ((conditionBound S P b).Q.eval (Fin.append w (Fin.snoc y t : Fin (S.h + 1) → ZMod 2)))
      = charOf S.m (S.Q.eval (Fin.append (w + t • P.pauli.X) y)) * shiftFactor P b w ^ t.val := by
  change charOf (conditionPrecision S.m P)
      (DiagPhase.eval (shiftSubst Fin.castSucc P.pauli.X (MvPolynomial.X (Fin.last (n + S.h)))
        (FTQCLib.Hilbert.liftTo (conditionPrecision S.m P) (le_conditionPrecision S.m P) S.Q)
      + MvPolynomial.X (Fin.last (n + S.h))
        * branchPhase (conditionPrecision S.m P) (fun j => (Fin.castAdd S.h j).castSucc) P b)
        (Fin.append w (Fin.snoc y t : Fin (S.h + 1) → ZMod 2))) = _
  rw [Fin.append_snoc]
  have hlast : DiagPhase.eval (MvPolynomial.X (Fin.last (n + S.h)) :
      DiagPhase (n + S.h + 1) (conditionPrecision S.m P)) (Fin.snoc (Fin.append w y) t)
      = (t.val : ZMod (2 ^ conditionPrecision S.m P)) := by
    rw [DiagPhase.eval_X, Fin.snoc_last]
  rw [DiagPhase.eval_add, DiagPhase.eval_mul, hlast,
    shiftSubst_eval _ _ _ _ _ t hlast, charOf_add, charOf_val_mul,
    charOf_branchPhase_eval _ _ _ (one_le_conditionPrecision S.m P)
      (fun h => two_le_conditionPrecision h)]
  rw [charOf_eval_liftTo]
  simp only [Fin.snoc_castSucc]
  rw [append_add_mul_append]
  congr 2
  unfold shiftFactor
  congr 5
  funext j
  simp only [Fin.append_left]

/-- **The bound constructor on support.** Its on-support amplitude is half the input's at `w`
plus the factor times the input's at `w + a`. -/
theorem ampCore_conditionBound (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2)
    (w : Fin n → ZMod 2) :
    ampCore (conditionBound S P b).m (conditionBound S P b).h (conditionBound S P b).Q
        (conditionBound S P b).c w
      = 1 / 2 * (ampCore S.m S.h S.Q S.c w
          + shiftFactor P b w * ampCore S.m S.h S.Q S.c (w + P.pauli.X)) := by
  unfold ampCore
  simp only [exp_realPhase_eq_charOf]
  change (S.c / (Real.sqrt 2 : ℂ)) / (Real.sqrt 2 : ℂ) ^ (S.h + 1)
      * ∑ y : Fin (S.h + 1) → ZMod 2, charOf (conditionBound S P b).m
          ((conditionBound S P b).Q.eval (Fin.append w y)) = _
  rw [← Equiv.sum_comp (Fin.snocEquiv fun _ => ZMod 2)]
  rw [Fintype.sum_prod_type, sum_zmod_two]
  change (S.c / (Real.sqrt 2 : ℂ)) / (Real.sqrt 2 : ℂ) ^ (S.h + 1)
      * (∑ y : Fin S.h → ZMod 2, charOf (conditionBound S P b).m
          ((conditionBound S P b).Q.eval (Fin.append w (Fin.snoc y 0 : Fin (S.h + 1) → ZMod 2)))
        + ∑ y : Fin S.h → ZMod 2, charOf (conditionBound S P b).m
          ((conditionBound S P b).Q.eval (Fin.append w (Fin.snoc y 1 : Fin (S.h + 1) → ZMod 2))))
      = _
  simp only [charOf_conditionBound_term, zero_smul, add_zero, one_smul,
    show ((0 : ZMod 2).val) = 0 from rfl, show ((1 : ZMod 2).val) = 1 from rfl, pow_zero,
    pow_one, mul_one]
  rw [← Finset.sum_mul, pow_succ]
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_sqrt_two_ne_zero
  have hp : (Real.sqrt 2 : ℂ) ^ S.h ≠ 0 := pow_ne_zero _ hs
  field_simp
  linear_combination (-S.c * ((∑ y : Fin S.h → ZMod 2,
      charOf S.m (S.Q.eval (Fin.append w y)))
    + (∑ y : Fin S.h → ZMod 2, charOf S.m (S.Q.eval (Fin.append (w + P.pauli.X) y)))
      * shiftFactor P b w)) * sqrt_two_sq_complex

/-- `w + a` is on the support exactly when `w` is, for `a` in the shadow. -/
theorem mem_support_add_iff (S : KernelSumState n) {a : Fin n → ZMod 2}
    (ha : a ∈ Submodule.map xProj S.L) (w : Fin n → ZMod 2) :
    (∃ p ∈ S.L, w + a = S.x₀ + p.X) ↔ (∃ p ∈ S.L, w = S.x₀ + p.X) := by
  rw [mem_support_iff, mem_support_iff, show w + a - S.x₀ = (w - S.x₀) + a from by abel]
  exact Submodule.add_mem_iff_left _ ha

/-- **The bound constructor's amplitude.** For `P`'s X-part in the shadow, the bound constructor
computes the projection. -/
theorem amp_conditionBound (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2)
    (hP : P.pauli.X ∈ Submodule.map xProj S.L) :
    amp (conditionBound S P b) = pauliProjection P b (amp S) := by
  funext w
  rw [pauliProjection_apply]
  have hL : ∀ v : Fin n → ZMod 2,
      (∃ p ∈ (conditionBound S P b).L, v = (conditionBound S P b).x₀ + p.X)
        ↔ (∃ p ∈ S.L, v = S.x₀ + p.X) := fun _ => Iff.rfl
  by_cases hw : ∃ p ∈ S.L, w = S.x₀ + p.X
  · rw [amp_pos ((hL w).mpr hw), ampCore_conditionBound, amp_pos hw,
      amp_pos ((mem_support_add_iff S hP w).mpr hw)]
  · rw [amp_neg (fun h => hw ((hL w).mp h)), amp_neg hw,
      amp_neg (fun h => hw ((mem_support_add_iff S hP w).mp h))]
    ring

/-- One summand of the raise constructor: the input's exponent at the word shifted by `t(w)·a`,
times the `t(w)`-th power of the factor, where `t(w) = u·x₀ + u·w`. -/
private theorem charOf_conditionRaise_term (S : KernelSumState n) (P : SignedPauli n)
    (b : ZMod 2) (u : Fin n → ZMod 2) (w : Fin n → ZMod 2) (y : Fin S.h → ZMod 2) :
    charOf (conditionRaise S P b u).m ((conditionRaise S P b u).Q.eval (Fin.append w y))
      = charOf S.m (S.Q.eval (Fin.append (w + (dotF2 u S.x₀ + dotF2 u w) • P.pauli.X) y))
        * shiftFactor P b w ^ (dotF2 u S.x₀ + dotF2 u w).val := by
  change charOf (conditionPrecision S.m P)
      (DiagPhase.eval (shiftSubst id P.pauli.X (xorForm (h := S.h) u (dotF2 u S.x₀))
        (FTQCLib.Hilbert.liftTo (conditionPrecision S.m P) (le_conditionPrecision S.m P) S.Q)
      + xorForm (h := S.h) u (dotF2 u S.x₀)
        * branchPhase (conditionPrecision S.m P) (Fin.castAdd S.h) P b) (Fin.append w y)) = _
  have hT : DiagPhase.eval (xorForm (h := S.h) (m := conditionPrecision S.m P) u
      (dotF2 u S.x₀)) (Fin.append w y)
      = ((dotF2 u S.x₀ + dotF2 u w).val : ZMod (2 ^ conditionPrecision S.m P)) := by
    rw [xorForm_eval]
    simp only [Fin.append_left]
  rw [DiagPhase.eval_add, DiagPhase.eval_mul, hT, shiftSubst_eval _ _ _ _ _ _ hT, charOf_add,
    charOf_val_mul, charOf_branchPhase_eval _ _ _ (one_le_conditionPrecision S.m P)
      (fun h => two_le_conditionPrecision h)]
  rw [charOf_eval_liftTo]
  simp only [id]
  rw [append_add_mul_append]
  congr 2
  unfold shiftFactor
  congr 5
  funext j
  simp only [Fin.append_left]

/-- **The raise constructor on support.** Its on-support amplitude is half the factor's `t(w)`-th
power times the input's at `w + t(w)·a`. -/
theorem ampCore_conditionRaise (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2)
    (u : Fin n → ZMod 2) (w : Fin n → ZMod 2) :
    ampCore (conditionRaise S P b u).m (conditionRaise S P b u).h (conditionRaise S P b u).Q
        (conditionRaise S P b u).c w
      = 1 / 2 * (shiftFactor P b w ^ (dotF2 u S.x₀ + dotF2 u w).val
          * ampCore S.m S.h S.Q S.c (w + (dotF2 u S.x₀ + dotF2 u w) • P.pauli.X)) := by
  unfold ampCore
  simp only [exp_realPhase_eq_charOf]
  change S.c / 2 / (Real.sqrt 2 : ℂ) ^ S.h
      * ∑ y : Fin S.h → ZMod 2, charOf (conditionRaise S P b u).m
          ((conditionRaise S P b u).Q.eval (Fin.append w y)) = _
  simp only [charOf_conditionRaise_term]
  rw [← Finset.sum_mul]
  ring

/-- **The shadow of the raise constructor.** On a co-isotropic `L`, with a separator `u` of `a`
from the shadow, the shadow of `(L ∩ P^⊥) + ⟨P⟩` is `π_X(L) + ⟨a⟩`: the Z-type Pauli `Z^u` lies in
`L^⊥ ≤ L` and anticommutes with `P`, so adding it moves any element of `L` into `P^⊥` without
changing its X-part. -/
theorem map_xProj_conditionRaise_L (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n)
    (b : ZMod 2) {u : Fin n → ZMod 2}
    (hu : Separates (Submodule.map xProj S.L) P.pauli.X u) :
    Submodule.map xProj (conditionRaise S P b u).L
      = Submodule.map xProj S.L ⊔ Submodule.span (ZMod 2) {P.pauli.X} := by
  have hspan : Submodule.map xProj (Submodule.span (ZMod 2) {P.pauli})
      = Submodule.span (ZMod 2) {P.pauli.X} := by
    rw [Submodule.map_span, Set.image_singleton, xProj_apply]
  change Submodule.map xProj ((S.L ⊓ LinearMap.BilinForm.orthogonal omegaBilin
      (Submodule.span (ZMod 2) {P.pauli})) ⊔ Submodule.span (ZMod 2) {P.pauli}) = _
  rw [Submodule.map_sup, hspan]
  congr 1
  refine le_antisymm (Submodule.map_mono inf_le_left) ?_
  have hzL : zPauli u ∈ S.L := by
    refine horth (fun r hr => ?_)
    change omega r (zPauli u) = 0
    rw [omega_comm, omega_zPauli]
    exact hu.1 _ (Submodule.mem_map_of_mem hr)
  have hzP : omega P.pauli (zPauli u) = 1 := by
    rw [omega_comm, omega_zPauli]
    exact hu.2
  rintro v ⟨p, hp, rfl⟩
  refine ⟨p + omega P.pauli p • zPauli u, Submodule.mem_inf.mpr ⟨Submodule.add_mem _ hp
    (Submodule.smul_mem _ _ hzL), ?_⟩, ?_⟩
  · intro q hq
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
    change omega (c • P.pauli) (p + omega P.pauli p • zPauli u) = 0
    rw [omega_smul_left, omega_add_right, omega_smul_right, hzP, mul_one, CharTwo.add_self_eq_zero,
      mul_zero]
  · simp only [xProj_apply, X_add, X_smul, zPauli_X, smul_zero, add_zero]

/-- **The raise constructor's amplitude.** On a co-isotropic `L`, for `P`'s X-part off the shadow
and any separator `u`, the raise constructor computes the projection: on `x₀ + π_X(L)` the selector
is `0` and only `f` survives; on `x₀ + a + π_X(L)` it is `1` and only `P f` survives; elsewhere
both sides vanish. -/
theorem amp_conditionRaise (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n)
    (b : ZMod 2) {u : Fin n → ZMod 2}
    (hu : Separates (Submodule.map xProj S.L) P.pauli.X u) :
    amp (conditionRaise S P b u) = pauliProjection P b (amp S) := by
  funext w
  rw [pauliProjection_apply]
  have hnot : P.pauli.X ∉ Submodule.map xProj S.L := fun h => by
    have h1 := hu.1 _ h
    rw [hu.2] at h1
    exact absurd h1 (by decide)
  have hsupp : ∀ v : Fin n → ZMod 2,
      (∃ p ∈ (conditionRaise S P b u).L, v = (conditionRaise S P b u).x₀ + p.X)
        ↔ v - S.x₀ ∈ Submodule.map xProj S.L ⊔ Submodule.span (ZMod 2) {P.pauli.X} := by
    intro v
    rw [mem_support_iff, map_xProj_conditionRaise_L S horth P b hu]
    rfl
  have ht : dotF2 u S.x₀ + dotF2 u w = dotF2 u (w - S.x₀) := by
    rw [dotF2_sub_right]
    exact (show ∀ x y : ZMod 2, x + y = y - x by decide) _ _
  have hshift : w + P.pauli.X - S.x₀ = (w - S.x₀) + P.pauli.X := by abel
  by_cases hw : w - S.x₀ ∈ Submodule.map xProj S.L
  · have ht0 : dotF2 u S.x₀ + dotF2 u w = 0 := by rw [ht]; exact hu.1 _ hw
    have hwa : ¬ ∃ p ∈ S.L, w + P.pauli.X = S.x₀ + p.X := by
      rw [mem_support_iff, hshift]
      exact fun h => hnot ((Submodule.add_mem_iff_right _ hw).mp h)
    rw [amp_pos ((hsupp w).mpr (Submodule.mem_sup_left hw)), ampCore_conditionRaise, ht0,
      amp_pos ((mem_support_iff S w).mpr hw), amp_neg hwa, zero_smul, add_zero]
    simp only [show ((0 : ZMod 2).val) = 0 from rfl, pow_zero, one_mul, mul_zero, add_zero]
  by_cases hwa : w + P.pauli.X - S.x₀ ∈ Submodule.map xProj S.L
  · have hdiff : w - S.x₀ = (w + P.pauli.X - S.x₀) - P.pauli.X := by abel
    have ht1 : dotF2 u S.x₀ + dotF2 u w = 1 := by
      rw [ht, hdiff, dotF2_sub_right, hu.1 _ hwa, hu.2]
      decide
    have hmem : w - S.x₀ ∈ Submodule.map xProj S.L ⊔ Submodule.span (ZMod 2) {P.pauli.X} := by
      rw [hdiff]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hwa)
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    rw [amp_pos ((hsupp w).mpr hmem), ampCore_conditionRaise, ht1, one_smul,
      amp_neg (fun h => hw ((mem_support_iff S w).mp h)),
      amp_pos ((mem_support_iff S _).mpr hwa)]
    simp only [show ((1 : ZMod 2).val) = 1 from rfl, pow_one, zero_add]
  · have hout : ¬ ∃ p ∈ (conditionRaise S P b u).L, w = (conditionRaise S P b u).x₀ + p.X := by
      rw [hsupp]
      intro hmem
      obtain ⟨v₁, hv₁, z, hz, hsum⟩ := Submodule.mem_sup.mp hmem
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hc : w - S.x₀ - c • P.pauli.X ∈ Submodule.map xProj S.L := by
        rw [← hsum, add_sub_cancel_right]
        exact hv₁
      rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) c with h0 | h1
      · rw [h0, zero_smul, sub_zero] at hc
        exact hw hc
      · rw [h1, one_smul] at hc
        refine hwa ?_
        have heq : w + P.pauli.X - S.x₀ = (w - S.x₀ - P.pauli.X) + (P.pauli.X + P.pauli.X) := by
          abel
        rw [heq, add_self_word, add_zero]
        exact hc
    rw [amp_neg hout, amp_neg (fun h => hw ((mem_support_iff S w).mp h)),
      amp_neg (fun h => hwa ((mem_support_iff S _).mp h))]
    ring

/-! ## The cover and the amplitude -/

/-- **The cover.** On a co-isotropic Lagrangian, the test `P.X ∈ π_X(L)` chooses exactly one
constructor, and that constructor's amplitude is the projection `½(S + (−1)^b · P S)`: the bound
constructor in the shadow; off it, the raise constructor with a separator, and the raise
constructor's amplitude is the projection for every separator. Proved at T10.3.1. -/
theorem condition_cover (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n)
    (b : ZMod 2) :
    Xor' (P.pauli.X ∈ Submodule.map xProj S.L ∧ condition S P b = conditionBound S P b
            ∧ amp (conditionBound S P b) = pauliProjection P b (amp S))
      (P.pauli.X ∉ Submodule.map xProj S.L
        ∧ (∃ u : Fin n → ZMod 2, Separates (Submodule.map xProj S.L) P.pauli.X u
            ∧ condition S P b = conditionRaise S P b u)
        ∧ ∀ u : Fin n → ZMod 2, Separates (Submodule.map xProj S.L) P.pauli.X u →
            amp (conditionRaise S P b u) = pauliProjection P b (amp S)) := by
  by_cases hP : P.pauli.X ∈ Submodule.map xProj S.L
  · exact Or.inl ⟨⟨hP, condition_of_mem hP b, amp_conditionBound S P b hP⟩, fun h => h.1 hP⟩
  · have hsep := Classical.epsilon_spec (exists_separates hP)
    refine Or.inr ⟨⟨hP, ⟨_, hsep, ?_⟩, fun u hu => amp_conditionRaise S horth P b hu⟩,
      fun h => hP h.1⟩
    unfold condition
    exact if_neg hP

/-- **The amplitude of conditioning.** At any height and any precision, for every Pauli with its
sign and every outcome, conditioning a carrier state with a co-isotropic Lagrangian has amplitude
`½(S + (−1)^b · P S)`; an impossible outcome has amplitude zero. Proved at T10.3.1. -/
theorem amp_condition (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n)
    (b : ZMod 2) : amp (condition S P b) = pauliProjection P b (amp S) := by
  rcases condition_cover S horth P b with ⟨⟨_, hcond, hamp⟩, _⟩ | ⟨⟨_, ⟨u, hu, hcond⟩, hamp⟩, _⟩
  · rw [hcond, hamp]
  · rw [hcond, hamp u hu]

/-- **The referee at `Z_j`.** Conditioning on `Z_j` with sign `+` at outcome `b` keeps the free
words with `w_j = b` and zeroes the rest, whatever the function. -/
theorem pauliProjection_zPauli_single (j : Fin n) (b : ZMod 2) (f : (Fin n → ZMod 2) → ℂ)
    (w : Fin n → ZMod 2) :
    pauliProjection ⟨0, zPauli (Pi.single j 1)⟩ b f w = if w j = b then f w else 0 := by
  have hz : ∀ v : Fin n → ZMod 2, zDot (zPauli (Pi.single j 1)) v = (v j).val := by
    intro v
    unfold zDot
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [zPauli, hi]) (by simp)]
    simp [zPauli]
  have hy : yWeight (zPauli (Pi.single j 1 : Fin n → ZMod 2)) = 0 := by
    unfold yWeight
    rw [hz]
    rfl
  have hX : (zPauli (Pi.single j 1 : Fin n → ZMod 2)).X = 0 := rfl
  simp only [pauliProjection, SignedPauli.act, pauliAct, hy, hX, hz, add_zero, pow_zero,
    one_mul, ZMod.val_zero]
  have hbit : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hbit b with hb | hb <;> rcases hbit (w j) with hw | hw <;> rw [hb, hw] <;>
    norm_num [ZMod.val_one] <;> ring

/-! ## The outcome as a new last free bit -/

/-- The variables of an exponent on `n` free bits, read on `n + 1` free bits: the free block goes
to the first `n` free bits and the bound block follows the new last free bit. -/
def appendVar (n h : ℕ) : Fin (n + h) → Fin (n + 1 + h) :=
  Fin.append (fun i : Fin n => Fin.castAdd h i.castSucc) (fun y : Fin h => Fin.natAdd (n + 1) y)

/-- The first `n` qubits of a Pauli on `n + 1`. -/
def pauliInit : Pauli (n + 1) →ₗ[ZMod 2] Pauli n where
  toFun p := ⟨Fin.init p.X, Fin.init p.Z⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Z-part of a Pauli on `n + 1` at the last qubit. -/
def lastZ : Pauli (n + 1) →ₗ[ZMod 2] ZMod 2 where
  toFun p := p.Z (Fin.last n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The input with a new last free bit on which the amplitude does not depend: the exponent reads
the first `n` free bits, and the Lagrangian is `L ⊕ ⟨X_last⟩`, so the support is the input's times
`𝔽₂`. The scale is unchanged (D3), so the amplitude at `w` is the input's at `init w`. -/
noncomputable def appendFreeBit (S : KernelSumState n) : KernelSumState (n + 1) where
  m := S.m
  h := S.h
  Q := MvPolynomial.rename (appendVar n S.h) S.Q
  c := S.c
  L := Submodule.comap pauliInit S.L ⊓ LinearMap.ker lastZ
  x₀ := Fin.snoc S.x₀ 0

/-- `P ⊗ Z` on one more qubit, the last, with `P`'s sign. On the fibre `b` of the last free bit
`½(1 + P ⊗ Z)` is `Π_b = ½(1 + (−1)^b P)`. -/
def SignedPauli.appendZ (P : SignedPauli n) : SignedPauli (n + 1) :=
  ⟨P.sign, ⟨Fin.snoc P.pauli.X 0, Fin.snoc P.pauli.Z 1⟩⟩

/-- **Conditioning with the outcome as a new last free bit** (D2 as revised): the one carrier state
`Σ_b ∣b⟩ ⊗ Π_b f`, which is what measuring `P` through an ancilla and deferring the measurement
gives. It is `condition` on `appendFreeBit S` and `P ⊗ Z` at outcome `0`, so it is the same cover,
chosen by the same test. -/
noncomputable def conditionOutcome (S : KernelSumState n) (P : SignedPauli n) :
    KernelSumState (n + 1) :=
  condition (appendFreeBit S) P.appendZ 0

/-- The symplectic form on `n + 1` qubits is the form on the first `n` plus the last qubit's
terms. -/
theorem omega_succ (p q : Pauli (n + 1)) :
    omega p q = omega (pauliInit p) (pauliInit q)
      + (p.Z (Fin.last n) * q.X (Fin.last n) + p.X (Fin.last n) * q.Z (Fin.last n)) := by
  unfold omega
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  change _ = (∑ i : Fin n, p.Z i.castSucc * q.X i.castSucc)
      + (∑ i : Fin n, p.X i.castSucc * q.Z i.castSucc) + _
  ring

/-- A Pauli on `n` qubits extended by `(X, Z)`-parts `x` and `0` at the last qubit. -/
def pauliSnoc (p : Pauli n) (x : ZMod 2) : Pauli (n + 1) :=
  ⟨Fin.snoc p.X x, Fin.snoc p.Z 0⟩

/-- The extension restricts back to the Pauli. -/
theorem pauliInit_pauliSnoc (p : Pauli n) (x : ZMod 2) :
    pauliInit (pauliSnoc p x) = p := by
  ext i
  · change (Fin.snoc p.X x : Fin (n + 1) → ZMod 2) i.castSucc = p.X i
    rw [Fin.snoc_castSucc]
  · change (Fin.snoc p.Z 0 : Fin (n + 1) → ZMod 2) i.castSucc = p.Z i
    rw [Fin.snoc_castSucc]

/-- The extension lies in the Lagrangian of `appendFreeBit` when the Pauli lies in the input's. -/
private theorem pauliSnoc_mem {S : KernelSumState n} {p : Pauli n} (hp : p ∈ S.L) (x : ZMod 2) :
    pauliSnoc p x ∈ (appendFreeBit S).L := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · change pauliInit (pauliSnoc p x) ∈ S.L
    rw [pauliInit_pauliSnoc]
    exact hp
  · change (Fin.snoc p.Z 0 : Fin (n + 1) → ZMod 2) (Fin.last n) = 0
    rw [Fin.snoc_last]

/-- **Appending a free bit keeps co-isotropy.** An element of the orthogonal of `L ⊕ ⟨X_last⟩`
has Z-part `0` at the last qubit, against `X_last`, and restricts into `L^⊥ ≤ L`, against the
extensions of `L`'s elements. -/
theorem orthogonal_appendFreeBit_le (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) :
    LinearMap.BilinForm.orthogonal omegaBilin (appendFreeBit S).L ≤ (appendFreeBit S).L := by
  intro q hq
  have hqr : ∀ r ∈ (appendFreeBit S).L, omega r q = 0 := fun r hr => hq r hr
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · refine horth (fun r hr => ?_)
    change omega r (pauliInit q) = 0
    have h := hqr _ (pauliSnoc_mem hr 0)
    rw [omega_succ, pauliInit_pauliSnoc] at h
    change omega r (pauliInit q)
      + ((Fin.snoc r.Z 0 : Fin (n + 1) → ZMod 2) (Fin.last n) * q.X (Fin.last n)
        + (Fin.snoc r.X 0 : Fin (n + 1) → ZMod 2) (Fin.last n) * q.Z (Fin.last n)) = 0 at h
    rw [Fin.snoc_last, Fin.snoc_last, zero_mul, zero_mul, add_zero, add_zero] at h
    exact h
  · have h := hqr _ (pauliSnoc_mem (Submodule.zero_mem S.L) 1)
    rw [omega_succ, pauliInit_pauliSnoc] at h
    change omega 0 (pauliInit q)
      + ((Fin.snoc (0 : Pauli n).Z 0 : Fin (n + 1) → ZMod 2) (Fin.last n) * q.X (Fin.last n)
        + (Fin.snoc (0 : Pauli n).X 1 : Fin (n + 1) → ZMod 2) (Fin.last n)
          * q.Z (Fin.last n)) = 0 at h
    rw [Fin.snoc_last, Fin.snoc_last, zero_mul, one_mul, zero_add] at h
    have h0 : omega (0 : Pauli n) (pauliInit q) = 0 := by
      simp only [omega, X_zero, Z_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    rw [h0, zero_add] at h
    exact h

/-- The support of `appendFreeBit S` is the input's support times `𝔽₂`: `w` lies on it exactly when
`init w` lies on the input's. -/
theorem mem_support_appendFreeBit_iff (S : KernelSumState n) (w : Fin (n + 1) → ZMod 2) :
    (∃ p ∈ (appendFreeBit S).L, w = (appendFreeBit S).x₀ + p.X)
      ↔ (∃ p ∈ S.L, Fin.init w = S.x₀ + p.X) := by
  constructor
  · rintro ⟨p, hp, hw⟩
    refine ⟨pauliInit p, (Submodule.mem_inf.mp hp).1, ?_⟩
    rw [hw]
    funext i
    change (Fin.snoc S.x₀ 0 : Fin (n + 1) → ZMod 2) i.castSucc + p.X i.castSucc
      = S.x₀ i + p.X i.castSucc
    rw [Fin.snoc_castSucc]
  · rintro ⟨p, hp, hw⟩
    refine ⟨pauliSnoc p (w (Fin.last n)), pauliSnoc_mem hp _, ?_⟩
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change w (Fin.last n) = (Fin.snoc S.x₀ 0 : Fin (n + 1) → ZMod 2) (Fin.last n)
        + (Fin.snoc p.X (w (Fin.last n)) : Fin (n + 1) → ZMod 2) (Fin.last n)
      rw [Fin.snoc_last, Fin.snoc_last, zero_add]
    · change w j.castSucc = (Fin.snoc S.x₀ 0 : Fin (n + 1) → ZMod 2) j.castSucc
        + (Fin.snoc p.X (w (Fin.last n)) : Fin (n + 1) → ZMod 2) j.castSucc
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact congrFun hw j

/-- The renamed exponent of `appendFreeBit S` at `(w, y)` is the input's at `(init w, y)`. -/
private theorem eval_appendFreeBit_Q (S : KernelSumState n) (w : Fin (n + 1) → ZMod 2)
    (y : Fin S.h → ZMod 2) :
    DiagPhase.eval (MvPolynomial.rename (appendVar n S.h) S.Q) (Fin.append w y)
      = DiagPhase.eval S.Q (Fin.append (Fin.init w) y) := by
  unfold DiagPhase.eval
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun g => MvPolynomial.eval g S.Q) (funext fun l => ?_)
  refine Fin.addCases (fun i => ?_) (fun j => ?_) l
  · simp only [Function.comp_apply, appendVar, Fin.append_left, DiagPhase.liftBinary, Fin.init]
  · simp only [Function.comp_apply, appendVar, Fin.append_right, DiagPhase.liftBinary]

/-- **The amplitude of `appendFreeBit`**: the input's amplitude at the first `n` free bits, so it
does not depend on the last. -/
theorem amp_appendFreeBit (S : KernelSumState n) :
    amp (appendFreeBit S) = fun w => amp S (Fin.init w) := by
  funext w
  by_cases hw : ∃ p ∈ S.L, Fin.init w = S.x₀ + p.X
  · rw [amp_pos ((mem_support_appendFreeBit_iff S w).mpr hw), amp_pos hw]
    unfold ampCore
    simp only [exp_realPhase_eq_charOf]
    change S.c / (Real.sqrt 2 : ℂ) ^ S.h * ∑ y : Fin S.h → ZMod 2,
        charOf S.m (DiagPhase.eval (MvPolynomial.rename (appendVar n S.h) S.Q) (Fin.append w y))
      = _
    simp only [eval_appendFreeBit_Q]
  · rw [amp_neg (fun h => hw ((mem_support_appendFreeBit_iff S w).mp h)), amp_neg hw]

/-- `P ⊗ Z` has the Y-count of `P`: the last qubit is `Z`. -/
theorem yWeight_appendZ (P : SignedPauli n) :
    yWeight P.appendZ.pauli = yWeight P.pauli := by
  unfold yWeight zDot
  rw [Fin.sum_univ_castSucc]
  change ∑ i : Fin n, ((Fin.snoc P.pauli.Z 1 : Fin (n + 1) → ZMod 2) i.castSucc).val
        * ((Fin.snoc P.pauli.X 0 : Fin (n + 1) → ZMod 2) i.castSucc).val
      + ((Fin.snoc P.pauli.Z 1 : Fin (n + 1) → ZMod 2) (Fin.last n)).val
        * ((Fin.snoc P.pauli.X 0 : Fin (n + 1) → ZMod 2) (Fin.last n)).val = _
  simp only [Fin.snoc_castSucc, Fin.snoc_last, ZMod.val_zero, mul_zero, add_zero]

/-- `X_j` has no Z-part, so its `zDot` with every word is zero. -/
theorem zDot_paulix (j : Fin n) (w : Fin n → ZMod 2) : zDot (paulix j) w = 0 := by
  simp only [zDot, paulix_Z, Pi.zero_apply, ZMod.val_zero, zero_mul, Finset.sum_const_zero]

/-- `X_j` has no Y: its Z-part is zero. So conditioning on it needs no precision above the
register's. -/
theorem yWeight_paulix (j : Fin n) : yWeight (paulix j) = 0 :=
  zDot_paulix j _

/-- `P ⊗ Z`'s sign exponent at `w` is `P`'s at `init w` plus the last bit. -/
private theorem zDot_appendZ (P : SignedPauli n) (w : Fin (n + 1) → ZMod 2) :
    zDot P.appendZ.pauli (w + P.appendZ.pauli.X)
      = zDot P.pauli (Fin.init w + P.pauli.X) + (w (Fin.last n)).val := by
  unfold zDot
  rw [Fin.sum_univ_castSucc]
  change ∑ i : Fin n, ((Fin.snoc P.pauli.Z 1 : Fin (n + 1) → ZMod 2) i.castSucc).val
        * ((w + (Fin.snoc P.pauli.X 0 : Fin (n + 1) → ZMod 2)) i.castSucc).val
      + ((Fin.snoc P.pauli.Z 1 : Fin (n + 1) → ZMod 2) (Fin.last n)).val
        * ((w + (Fin.snoc P.pauli.X 0 : Fin (n + 1) → ZMod 2)) (Fin.last n)).val = _
  simp only [Pi.add_apply, Fin.snoc_castSucc, Fin.snoc_last, add_zero, Fin.init]
  rw [show ((1 : ZMod 2).val) = 1 from rfl, one_mul]

/-- The shift of `P ⊗ Z` restricts to the shift of `P`. -/
private theorem init_add_appendZ (P : SignedPauli n) (w : Fin (n + 1) → ZMod 2) :
    Fin.init (w + P.appendZ.pauli.X) = Fin.init w + P.pauli.X := by
  funext i
  change w i.castSucc + (Fin.snoc P.pauli.X 0 : Fin (n + 1) → ZMod 2) i.castSucc
    = w i.castSucc + P.pauli.X i
  rw [Fin.snoc_castSucc]

/-- **`½(1 + P ⊗ Z)` is `Π_b` on the fibre `b`.** On a function of the first `n` free bits, the
projection of `P ⊗ Z` at outcome `0` is, at `w`, the projection of `P` at outcome `w_last`. -/
theorem pauliProjection_appendZ (P : SignedPauli n) (f : (Fin n → ZMod 2) → ℂ)
    (w : Fin (n + 1) → ZMod 2) :
    pauliProjection P.appendZ 0 (fun v => f (Fin.init v)) w
      = pauliProjection P (w (Fin.last n)) f (Fin.init w) := by
  rw [pauliProjection_apply, pauliProjection_apply, init_add_appendZ]
  unfold shiftFactor
  rw [yWeight_appendZ, zDot_appendZ, pow_add]
  change 1 / 2 * (f (Fin.init w) + (-1 : ℂ) ^ (0 : ZMod 2).val * ((-1 : ℂ) ^ P.sign.val
      * (Complex.I ^ yWeight P.pauli * ((-1 : ℂ) ^ zDot P.pauli (Fin.init w + P.pauli.X)
        * (-1 : ℂ) ^ (w (Fin.last n)).val))) * f (Fin.init w + P.pauli.X)) = _
  rw [ZMod.val_zero, pow_zero]
  ring

/-- **The amplitude of the outcome-bit form.** At `(w, b)`, with `b` the last free bit, it is the
projection `Π_b` of the input's amplitude at `w`. Proved at T10.3.2. -/
theorem amp_conditionOutcome (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n) :
    amp (conditionOutcome S P)
      = fun w => pauliProjection P (w (Fin.last n)) (amp S) (Fin.init w) := by
  unfold conditionOutcome
  rw [amp_condition _ (orthogonal_appendFreeBit_le S horth), amp_appendFreeBit]
  funext w
  exact pauliProjection_appendZ P (amp S) w

/-- **The evaluations of the outcome bit.** Evaluating the last free bit of the outcome-bit form at
`b` gives conditioning at outcome `b`. Proved at T10.3.2. -/
theorem conditionOutcome_eval (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n)
    (b : ZMod 2) :
    (fun w : Fin n → ZMod 2 => amp (conditionOutcome S P) (Fin.snoc w b : Fin (n + 1) → ZMod 2))
      = amp (condition S P b) := by
  rw [amp_conditionOutcome S horth P, amp_condition S horth P b]
  funext w
  simp only [Fin.init_snoc, Fin.snoc_last]

/-! ## The outcome-bit form keeps the carrier property -/

/-- The outcome-bit form is at the conditioning precision. -/
theorem conditionOutcome_m (S : KernelSumState n) (P : SignedPauli n) :
    (conditionOutcome S P).m = conditionPrecision S.m P.appendZ := by
  unfold conditionOutcome condition
  split_ifs <;> rfl

/-- At a positive precision `m`, with `2 ≤ m` for an odd number of Y, the conditioning precision
is `m`. -/
theorem conditionPrecision_eq {n m : ℕ} (P : SignedPauli n) (hm : 1 ≤ m)
    (hP : yWeight P.pauli % 2 = 1 → 2 ≤ m) : conditionPrecision m P = m := by
  unfold conditionPrecision
  split_ifs with h
  · exact max_eq_left hm
  · exact max_eq_left (hP (by omega))

/-- Appending a free bit keeps isotropy: the new Lagrangian's elements have Z-part `0` at the last
qubit, so their form is the form of their restrictions, which lie in `L`. -/
theorem isStabilizer_appendFreeBit {S : KernelSumState n}
    (hS : IsStabilizer S.L) : IsStabilizer (appendFreeBit S).L := by
  intro p hp q hq
  obtain ⟨hpL, hpZ⟩ := Submodule.mem_inf.mp hp
  obtain ⟨hqL, hqZ⟩ := Submodule.mem_inf.mp hq
  have hpz : p.Z (Fin.last n) = 0 := LinearMap.mem_ker.mp hpZ
  have hqz : q.Z (Fin.last n) = 0 := LinearMap.mem_ker.mp hqZ
  rw [omega_succ, hS _ hpL _ hqL, hpz, hqz, zero_mul, mul_zero, add_zero, add_zero]

/-- The raised Lagrangian `(L ∩ P^⊥) + ⟨P⟩` is isotropic when `L` is: `P` commutes with itself and
with `L ∩ P^⊥`. -/
theorem isStabilizer_raise {N : ℕ} {L : Submodule (ZMod 2) (Pauli N)}
    (hL : IsStabilizer L) (P : Pauli N) :
    IsStabilizer ((L ⊓ LinearMap.BilinForm.orthogonal omegaBilin (Submodule.span (ZMod 2) {P}))
      ⊔ Submodule.span (ZMod 2) {P}) := by
  intro p hp q hq
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Submodule.mem_sup.mp hp
  obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := Submodule.mem_sup.mp hq
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp₂
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hq₂
  obtain ⟨hp₁L, hp₁P⟩ := Submodule.mem_inf.mp hp₁
  obtain ⟨hq₁L, hq₁P⟩ := Submodule.mem_inf.mp hq₁
  have hPp : omega P p₁ = 0 := hp₁P P (Submodule.mem_span_singleton_self P)
  have hPq : omega P q₁ = 0 := hq₁P P (Submodule.mem_span_singleton_self P)
  rw [omega_add_left, omega_add_right, omega_add_right, omega_smul_left, omega_smul_left,
    omega_smul_right, omega_smul_right, omega_comm p₁ P, hL _ hp₁L _ hq₁L, hPp, hPq, omega_self]
  ring

/-- The raised Lagrangian is co-isotropic when `L` is and a separator `u` of `P`'s X-part from the
shadow exists. The Z-type Pauli `Z^u` lies in `L^⊥ ≤ L` and anticommutes with `P`. An element `q`
orthogonal to the raised Lagrangian, shifted by `ω(Z^u, q) • P`, is orthogonal to `L`: each
`r ∈ L` is `r'` plus `ω(P, r) • Z^u` with `r' ∈ L ∩ P^⊥`. So the shifted `q` lies in `L`, and
in `P^⊥` since `q` and `P` do. -/
theorem orthogonal_raise_le {N : ℕ} {L : Submodule (ZMod 2) (Pauli N)}
    (horth : LinearMap.BilinForm.orthogonal omegaBilin L ≤ L) (P : Pauli N)
    {u : Fin N → ZMod 2} (hu : Separates (Submodule.map xProj L) P.X u) :
    LinearMap.BilinForm.orthogonal omegaBilin
        ((L ⊓ LinearMap.BilinForm.orthogonal omegaBilin (Submodule.span (ZMod 2) {P}))
          ⊔ Submodule.span (ZMod 2) {P})
      ≤ (L ⊓ LinearMap.BilinForm.orthogonal omegaBilin (Submodule.span (ZMod 2) {P}))
          ⊔ Submodule.span (ZMod 2) {P} := by
  have hzL : zPauli u ∈ L := by
    refine horth (fun r hr => ?_)
    change omega r (zPauli u) = 0
    rw [omega_comm, omega_zPauli]
    exact hu.1 _ (Submodule.mem_map_of_mem hr)
  have hzP : omega P (zPauli u) = 1 := by
    rw [omega_comm, omega_zPauli]
    exact hu.2
  have hPmem : P ∈ Submodule.span (ZMod 2) {P} := Submodule.mem_span_singleton_self P
  intro q hq
  have hqr : ∀ r ∈ (L ⊓ LinearMap.BilinForm.orthogonal omegaBilin (Submodule.span (ZMod 2) {P}))
      ⊔ Submodule.span (ZMod 2) {P}, omega r q = 0 := fun r hr => hq r hr
  have hqP : omega P q = 0 := hqr P (Submodule.mem_sup_right hPmem)
  have hperp : ∀ v : Pauli N, omega P v = 0 →
      v ∈ LinearMap.BilinForm.orthogonal omegaBilin (Submodule.span (ZMod 2) {P}) := by
    intro v hv x hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change omega (d • P) v = 0
    rw [omega_smul_left, hv, mul_zero]
  have hshiftL : q + omega (zPauli u) q • P ∈ L := by
    refine horth (fun r hr => ?_)
    change omega r (q + omega (zPauli u) q • P) = 0
    have hr' : r + omega P r • zPauli u
        ∈ L ⊓ LinearMap.BilinForm.orthogonal omegaBilin (Submodule.span (ZMod 2) {P}) := by
      refine Submodule.mem_inf.mpr ⟨Submodule.add_mem _ hr (Submodule.smul_mem _ _ hzL),
        hperp _ ?_⟩
      rw [omega_add_right, omega_smul_right, hzP, mul_one, CharTwo.add_self_eq_zero]
    have h := hqr _ (Submodule.mem_sup_left hr')
    rw [omega_add_left, omega_smul_left] at h
    rw [omega_add_right, omega_smul_right, omega_comm r P]
    linear_combination h
  have hshift : q + omega (zPauli u) q • P
      ∈ L ⊓ LinearMap.BilinForm.orthogonal omegaBilin (Submodule.span (ZMod 2) {P}) := by
    refine Submodule.mem_inf.mpr ⟨hshiftL, hperp _ ?_⟩
    rw [omega_add_right, omega_smul_right, hqP, omega_self, mul_zero, add_zero]
  have hq_eq : q = (q + omega (zPauli u) q • P) + omega (zPauli u) q • P := by
    rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  rw [hq_eq]
  exact Submodule.add_mem_sup hshift (Submodule.smul_mem _ _ hPmem)

/-- Conditioning keeps an isotropic, co-isotropic Lagrangian: the bound constructor keeps `L`, and
the raise constructor's `(L ∩ P^⊥) + ⟨P⟩` is isotropic and co-isotropic. -/
theorem condition_L {N : ℕ} {T : KernelSumState N} (hT : IsStabilizer T.L)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin T.L ≤ T.L) (P : SignedPauli N)
    (b : ZMod 2) :
    IsStabilizer (condition T P b).L
      ∧ LinearMap.BilinForm.orthogonal omegaBilin (condition T P b).L ≤ (condition T P b).L := by
  unfold condition
  split_ifs with hP
  · exact ⟨hT, horth⟩
  · exact ⟨isStabilizer_raise hT P.pauli,
      orthogonal_raise_le horth P.pauli (Classical.epsilon_spec (exists_separates hP))⟩

/-- The two projections add up to the function: `Π_0 f + Π_1 f = f`. -/
theorem pauliProjection_zero_add_one {N : ℕ} (P : SignedPauli N)
    (f : (Fin N → ZMod 2) → ℂ) (w : Fin N → ZMod 2) :
    pauliProjection P 0 f w + pauliProjection P 1 f w = f w := by
  unfold pauliProjection
  have h0 : (0 : ZMod 2).val = 0 := rfl
  have h1 : (1 : ZMod 2).val = 1 := rfl
  rw [h0, h1, pow_zero, pow_one]
  ring

/-- The outcome-bit form of a nonzero amplitude is nonzero: at `(v, 0)` and `(v, 1)` it is
`Π_0 f (v)` and `Π_1 f (v)`, which add up to `f v`. -/
theorem amp_conditionOutcome_ne_zero (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (hne : amp S ≠ 0)
    (P : SignedPauli n) : amp (conditionOutcome S P) ≠ 0 := by
  rw [amp_conditionOutcome S horth P]
  intro h
  apply hne
  funext v
  have h0 := congrFun h (Fin.snoc v 0 : Fin (n + 1) → ZMod 2)
  have h1 := congrFun h (Fin.snoc v 1 : Fin (n + 1) → ZMod 2)
  simp only [Fin.init_snoc, Fin.snoc_last, Pi.zero_apply] at h0 h1
  rw [Pi.zero_apply, ← pauliProjection_zero_add_one P (amp S) v, h0, h1, add_zero]

/-- **The outcome-bit form of a carrier state is a carrier state.** -/
theorem isCarrier_conditionOutcome {S : KernelSumState n} (hS : IsCarrier S)
    (P : SignedPauli n) : IsCarrier (conditionOutcome S P) := by
  obtain ⟨_, hstab, horth, hne⟩ := hS
  obtain ⟨hL, hLorth⟩ := condition_L (isStabilizer_appendFreeBit hstab)
    (orthogonal_appendFreeBit_le S horth) P.appendZ 0
  refine ⟨?_, hL, hLorth, amp_conditionOutcome_ne_zero S horth hne P⟩
  rw [conditionOutcome_m]
  exact one_le_conditionPrecision _ _

/-- **Appending a free bit keeps the carrier property.** -/
theorem isCarrier_appendFreeBit {S : KernelSumState n} (hS : IsCarrier S) :
    IsCarrier (appendFreeBit S) := by
  refine ⟨hS.1, isStabilizer_appendFreeBit hS.2.1, orthogonal_appendFreeBit_le S hS.2.2.1,
    fun h0 => hS.2.2.2 ?_⟩
  funext v
  have hv := congrFun h0 (Fin.snoc v 0 : Fin (n + 1) → ZMod 2)
  rw [amp_appendFreeBit] at hv
  simpa only [Fin.init_snoc] using hv

/-! ## Relabelling the free bits -/

/-- The variables of an exponent with its free block relabelled by `σ`; the bound block is fixed. -/
def permuteVar (σ : Equiv.Perm (Fin n)) (h : ℕ) : Fin (n + h) → Fin (n + h) :=
  Fin.append (fun j : Fin n => Fin.castAdd h (σ j)) (fun y : Fin h => Fin.natAdd n y)

/-- **A relabelling of the free bits**: input bit `j` becomes output bit `σ j`. The exponent reads
the output word through `σ`, and the Lagrangian and the offset are relabelled by
`FTQCLib.Aut.pauliPermute σ`. -/
noncomputable def permuteFreeBits (σ : Equiv.Perm (Fin n)) (S : KernelSumState n) :
    KernelSumState n where
  m := S.m
  h := S.h
  Q := MvPolynomial.rename (permuteVar σ S.h) S.Q
  c := S.c
  L := Submodule.map (FTQCLib.Aut.pauliPermute σ).toLinearMap S.L
  x₀ := S.x₀ ∘ σ.symm

/-- The renamed exponent of a relabelling at `(w, y)` is the input's at `(w ∘ σ, y)`. -/
private theorem eval_permuteFreeBits_Q (σ : Equiv.Perm (Fin n)) (S : KernelSumState n)
    (w : Fin n → ZMod 2) (y : Fin S.h → ZMod 2) :
    DiagPhase.eval (MvPolynomial.rename (permuteVar σ S.h) S.Q) (Fin.append w y)
      = DiagPhase.eval S.Q (Fin.append (w ∘ σ) y) := by
  unfold DiagPhase.eval
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun g => MvPolynomial.eval g S.Q) (funext fun l => ?_)
  refine Fin.addCases (fun i => ?_) (fun y' => ?_) l
  · simp only [Function.comp_apply, permuteVar, Fin.append_left, DiagPhase.liftBinary]
  · simp only [Function.comp_apply, permuteVar, Fin.append_right, DiagPhase.liftBinary]

/-- The support of a relabelling is the input's support relabelled: `w` lies on it exactly when
`w ∘ σ` lies on the input's. -/
private theorem mem_support_permuteFreeBits_iff (σ : Equiv.Perm (Fin n)) (S : KernelSumState n)
    (w : Fin n → ZMod 2) :
    (∃ p ∈ (permuteFreeBits σ S).L, w = (permuteFreeBits σ S).x₀ + p.X)
      ↔ (∃ p ∈ S.L, w ∘ σ = S.x₀ + p.X) := by
  constructor
  · rintro ⟨p', hp', hw⟩
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hp'
    refine ⟨p, hp, funext fun i => ?_⟩
    have hi := congrFun hw (σ i)
    simpa [permuteFreeBits] using hi
  · rintro ⟨p, hp, hw⟩
    refine ⟨FTQCLib.Aut.pauliPermute σ p, Submodule.mem_map_of_mem hp, funext fun i => ?_⟩
    have hi := congrFun hw (σ.symm i)
    simpa [permuteFreeBits] using hi

/-- **The amplitude of a relabelling**: the input's amplitude precomposed with `σ`, at any height.
Proved at T10.3.3. -/
theorem amp_permuteFreeBits (σ : Equiv.Perm (Fin n)) (S : KernelSumState n) :
    amp (permuteFreeBits σ S) = fun w => amp S (w ∘ σ) := by
  funext w
  by_cases hw : ∃ p ∈ S.L, w ∘ σ = S.x₀ + p.X
  · rw [amp_pos ((mem_support_permuteFreeBits_iff σ S w).mpr hw), amp_pos hw]
    unfold ampCore
    simp only [exp_realPhase_eq_charOf]
    change S.c / (Real.sqrt 2 : ℂ) ^ S.h * ∑ y : Fin S.h → ZMod 2,
        charOf S.m (DiagPhase.eval (MvPolynomial.rename (permuteVar σ S.h) S.Q) (Fin.append w y))
      = _
    simp only [eval_permuteFreeBits_Q]
  · rw [amp_neg (fun h => hw ((mem_support_permuteFreeBits_iff σ S w).mp h)), amp_neg hw]

/-- **Relabelling the free bits keeps the carrier property**: `pauliPermute σ` keeps the
symplectic form, and the amplitude is the input's precomposed with `σ`. -/
theorem isCarrier_permuteFreeBits (σ : Equiv.Perm (Fin n)) {S : KernelSumState n}
    (hS : IsCarrier S) : IsCarrier (permuteFreeBits σ S) := by
  refine ⟨hS.1, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    change omega (FTQCLib.Aut.pauliPermute σ p) (FTQCLib.Aut.pauliPermute σ q) = 0
    rw [FTQCLib.Aut.pauliPermute_preserves_omega]
    exact hS.2.1 p hp q hq
  · intro x hx
    have hy : (FTQCLib.Aut.pauliPermute σ).symm x ∈ S.L := by
      refine hS.2.2.1 (LinearMap.BilinForm.mem_orthogonal_iff.mpr fun z hz => ?_)
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) (FTQCLib.Aut.pauliPermute σ z)
        (Submodule.mem_map_of_mem hz)
      change omega z ((FTQCLib.Aut.pauliPermute σ).symm x) = 0
      change omega (FTQCLib.Aut.pauliPermute σ z) x = 0 at h
      rw [← FTQCLib.Aut.pauliPermute_preserves_omega σ, LinearEquiv.apply_symm_apply]
      exact h
    refine Submodule.mem_map.mpr ⟨_, hy, ?_⟩
    exact LinearEquiv.apply_symm_apply _ x
  · intro h0
    apply hS.2.2.2
    funext v
    have hv := congrFun h0 (v ∘ σ.symm)
    rw [amp_permuteFreeBits] at hv
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using hv

/-! ## Dropping a free bit the support determines -/

/-- `u` reads bit `j` on `V`: it ignores bit `j` and agrees with the `j`-th coordinate on `V`.
Such a `u` exists exactly when `e_j ∉ V`; on the support coset `x₀ + V` bit `j` is then the affine
function `raiseConst j u x₀ + u·w` of the other bits. The data `hRaise` consumes. -/
def ReadsBit (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (j : Fin n) (u : Fin n → ZMod 2) : Prop :=
  u j = 0 ∧ ∀ v ∈ V, dotF2 u v = v j

/-- A Pauli on `n + 1` qubits with bit `j` removed, after the CNOTs from the bits `u` reads to bit
`j`: the X-part loses bit `j`, and the Z-part at bit `i` gains `Z_j·u_i`. On a Lagrangian whose
shadow `u` reads at `j`, every element then has X-part `0` at `j`, so removing `j` keeps it a
Lagrangian on `n` qubits with the removed shadow. -/
def dropPauli (j : Fin (n + 1)) (u : Fin (n + 1) → ZMod 2) : Pauli (n + 1) →ₗ[ZMod 2] Pauli n where
  toFun p :=
    ⟨fun i => p.X (j.succAbove i), fun i => p.Z (j.succAbove i) + p.Z j * u (j.succAbove i)⟩
  map_add' p q := by
    ext i
    · simp only [X_add, Pi.add_apply]
    · simp only [Z_add, Pi.add_apply]
      ring
  map_smul' c p := by
    ext i
    · simp only [X_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    · simp only [Z_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

/-- The substitution that drops free bit `j`: its variable becomes the XOR form of the value the
support determines, `raiseConst j u x₀ + u·w` over the other free bits, and the other variables are
renamed onto `n` free bits. -/
noncomputable def dropSubst {h m : ℕ} (j : Fin (n + 1)) (u x₀ : Fin (n + 1) → ZMod 2) :
    Fin (n + 1 + h) → DiagPhase (n + h) m :=
  Fin.append
    (Fin.insertNth (α := fun _ => DiagPhase (n + h) m) j
      (xorForm (h := h) (fun i => u (j.succAbove i)) (raiseConst j u x₀))
      (fun i : Fin n => MvPolynomial.X (Fin.castAdd h i)))
    (fun y : Fin h => MvPolynomial.X (Fin.natAdd n y))

/-- Dropping free bit `j` with the reader `u`: substitute the value the support determines for bit
`j` in the exponent (`dropSubst`), remove bit `j` from the Lagrangian (`dropPauli`) and from the
offset. The height, precision and scale are unchanged. -/
noncomputable def dropFreeBitBy (j : Fin (n + 1)) (u : Fin (n + 1) → ZMod 2)
    (S : KernelSumState (n + 1)) : KernelSumState n where
  m := S.m
  h := S.h
  Q := MvPolynomial.bind₁ (dropSubst j u S.x₀) S.Q
  c := S.c
  L := Submodule.map (dropPauli j u) S.L
  x₀ := fun i => S.x₀ (j.succAbove i)

/-- **Dropping a free bit the support determines**, by substitution, with a reader of bit `j`
chosen. Every theorem about it assumes `e_j ∉ π_X(L)`, which is exactly that the support
determines bit `j` and that a reader exists. -/
noncomputable def dropFreeBit (j : Fin (n + 1)) (S : KernelSumState (n + 1)) : KernelSumState n :=
  dropFreeBitBy j (Classical.epsilon (ReadsBit (Submodule.map xProj S.L) j)) S

/-- A reader of bit `j` exists off the shadow: `e_j` plus a functional that vanishes on `V` and
is `1` at `e_j`. No isotropy is needed. -/
theorem exists_readsBit {V : Submodule (ZMod 2) (Fin n → ZMod 2)} {j : Fin n}
    (hj : (Pi.single j 1 : Fin n → ZMod 2) ∉ V) : ∃ u, ReadsBit V j u := by
  obtain ⟨g, hgV, hgj⟩ := exists_separates hj
  rw [dotF2_single] at hgj
  refine ⟨Pi.single j 1 + g, ?_, fun v hv => ?_⟩
  · rw [Pi.add_apply, Pi.single_eq_same, hgj]
    decide
  · rw [dotF2_add_left, dotF2_single_left, hgV v hv, add_zero]

/-- The reader `dropFreeBit` chooses reads bit `j` when the support determines it. -/
private theorem readsBit_epsilon {j : Fin (n + 1)} {S : KernelSumState (n + 1)}
    (hj : (Pi.single j 1 : Fin (n + 1) → ZMod 2) ∉ Submodule.map xProj S.L) :
    ReadsBit (Submodule.map xProj S.L) j
      (Classical.epsilon (ReadsBit (Submodule.map xProj S.L) j)) :=
  Classical.epsilon_spec (exists_readsBit hj)

/-- The value the support determines for bit `j` at the other bits `w`, read by `u`:
`raiseConst j u x₀ + u·w`. -/
private def dropValue (j : Fin (n + 1)) (u x₀ : Fin (n + 1) → ZMod 2) (w : Fin n → ZMod 2) :
    ZMod 2 :=
  raiseConst j u x₀ + dotF2 (fun i => u (j.succAbove i)) w

/-- The substituted exponent at `(w, y)` is the input's at `(insertNth j β w, y)`, where `β` is
the value the support determines for bit `j`. -/
private theorem eval_dropSubst {h m : ℕ} (j : Fin (n + 1)) (u x₀ : Fin (n + 1) → ZMod 2)
    (Q : DiagPhase (n + 1 + h) m) (w : Fin n → ZMod 2) (y : Fin h → ZMod 2) :
    DiagPhase.eval (MvPolynomial.bind₁ (dropSubst (h := h) (m := m) j u x₀) Q) (Fin.append w y)
      = DiagPhase.eval Q
          (Fin.append (Fin.insertNth j (dropValue j u x₀ w) w : Fin (n + 1) → ZMod 2) y) := by
  unfold DiagPhase.eval
  have hb := MvPolynomial.aeval_bind₁ (R := ZMod (2 ^ m)) (S := ZMod (2 ^ m))
    (DiagPhase.liftBinary (Fin.append w y)) (dropSubst (h := h) (m := m) j u x₀) Q
  simp only [MvPolynomial.aeval_eq_eval] at hb
  rw [hb]
  congr 2
  funext l
  refine Fin.addCases (fun k => ?_) (fun i => ?_) l
  · simp only [dropSubst, Fin.append_left, DiagPhase.liftBinary]
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
    · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same, ← DiagPhase.eval, xorForm_eval]
      simp only [Fin.append_left, dropValue]
    · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove, MvPolynomial.eval_X]
      simp only [DiagPhase.liftBinary, Fin.append_left]
  · simp only [dropSubst, Fin.append_right, MvPolynomial.eval_X, DiagPhase.liftBinary]

/-- **Bit `j` on the support is the determined value.** If `insertNth j β w` lies on the support
and `u` reads bit `j` on the shadow, then `β` is `dropValue j u x₀ w`. -/
private theorem eq_dropValue_of_mem_support {j : Fin (n + 1)} {u : Fin (n + 1) → ZMod 2}
    {S : KernelSumState (n + 1)} (hu : ReadsBit (Submodule.map xProj S.L) j u)
    {w : Fin n → ZMod 2} {β : ZMod 2}
    (hv : ∃ p ∈ S.L, (Fin.insertNth j β w : Fin (n + 1) → ZMod 2) = S.x₀ + p.X) :
    β = dropValue j u S.x₀ w := by
  have hread := hu.2 _ ((mem_support_iff S _).mp hv)
  rw [dotF2_sub_right, dotF2_succAbove j u (Fin.insertNth j β w), hu.1] at hread
  simp only [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, Pi.sub_apply,
    zero_mul, zero_add] at hread
  unfold dropValue raiseConst
  generalize dotF2 (fun i => u (j.succAbove i)) w = a at hread ⊢
  generalize dotF2 u S.x₀ = d at hread ⊢
  generalize S.x₀ j = x at hread ⊢
  clear hv
  revert a d x β
  decide

/-- The support after dropping bit `j` is the support with bit `j` removed: `w` lies on it exactly
when its extension by the determined value lies on the input's. -/
private theorem mem_support_dropFreeBitBy_iff {j : Fin (n + 1)} {u : Fin (n + 1) → ZMod 2}
    {S : KernelSumState (n + 1)} (hu : ReadsBit (Submodule.map xProj S.L) j u)
    (w : Fin n → ZMod 2) :
    (∃ p ∈ (dropFreeBitBy j u S).L, w = (dropFreeBitBy j u S).x₀ + p.X)
      ↔ (∃ p ∈ S.L,
          (Fin.insertNth j (dropValue j u S.x₀ w) w : Fin (n + 1) → ZMod 2) = S.x₀ + p.X) := by
  constructor
  · rintro ⟨p', hp', hw⟩
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hp'
    have hrem : Fin.removeNth j (S.x₀ + p.X) = w := by
      rw [hw]
      rfl
    have hself := Fin.insertNth_self_removeNth j (S.x₀ + p.X)
    rw [hrem] at hself
    have hon : ∃ q ∈ S.L, (Fin.insertNth j ((S.x₀ + p.X) j) w : Fin (n + 1) → ZMod 2)
        = S.x₀ + q.X := ⟨p, hp, hself⟩
    rw [← eq_dropValue_of_mem_support hu hon]
    exact hon
  · rintro ⟨p, hp, hv⟩
    refine ⟨dropPauli j u p, Submodule.mem_map_of_mem hp, funext fun i => ?_⟩
    have hi := congrFun hv (j.succAbove i)
    rw [Fin.insertNth_apply_succAbove] at hi
    exact hi

/-- **The amplitude after dropping bit `j`, with a reader.** It is the input's at the extension
by the determined value. -/
private theorem amp_dropFreeBitBy {j : Fin (n + 1)} {u : Fin (n + 1) → ZMod 2}
    {S : KernelSumState (n + 1)} (hu : ReadsBit (Submodule.map xProj S.L) j u)
    (w : Fin n → ZMod 2) :
    amp (dropFreeBitBy j u S) w = amp S (Fin.insertNth j (dropValue j u S.x₀ w) w) := by
  by_cases hv : ∃ p ∈ S.L,
      (Fin.insertNth j (dropValue j u S.x₀ w) w : Fin (n + 1) → ZMod 2) = S.x₀ + p.X
  · rw [amp_pos ((mem_support_dropFreeBitBy_iff hu w).mpr hv), amp_pos hv]
    unfold ampCore
    simp only [exp_realPhase_eq_charOf]
    change S.c / (Real.sqrt 2 : ℂ) ^ S.h * ∑ y : Fin S.h → ZMod 2,
        charOf S.m (DiagPhase.eval (MvPolynomial.bind₁ (dropSubst j u S.x₀) S.Q)
          (Fin.append w y)) = _
    simp only [eval_dropSubst]
  · rw [amp_neg (fun h => hv ((mem_support_dropFreeBitBy_iff hu w).mp h)), amp_neg hv]

/-- The sum over a bit, started at `β`: the value at `β` plus the value at `β + 1`. -/
private theorem sum_zmod_two_from (F : ZMod 2 → ℂ) (β : ZMod 2) :
    ∑ t : ZMod 2, F t = F β + F (β + 1) := by
  rw [← Equiv.sum_comp (Equiv.addLeft β) F, sum_zmod_two]
  simp only [Equiv.coe_addLeft, add_zero]

/-- The lift of a Pauli on `n` qubits to `n + 1` that `dropPauli` undoes: bit `j` gets X-part
`u·X` over the other bits and Z-part `0`. -/
def liftPauli (j : Fin (n + 1)) (u : Fin (n + 1) → ZMod 2) (q : Pauli n) :
    Pauli (n + 1) :=
  ⟨Fin.insertNth j (dotF2 (fun i => u (j.succAbove i)) q.X) q.X, Fin.insertNth j 0 q.Z⟩

/-- `dropPauli` is adjoint to `liftPauli` under the symplectic form, for every reader. -/
theorem omega_dropPauli_left (j : Fin (n + 1)) (u : Fin (n + 1) → ZMod 2)
    (r : Pauli (n + 1)) (q : Pauli n) :
    omega (dropPauli j u r) q = omega r (liftPauli j u q) := by
  unfold omega
  rw [Fin.sum_univ_succAbove _ j, Fin.sum_univ_succAbove _ j]
  simp only [dropPauli, liftPauli, LinearMap.coe_mk, AddHom.coe_mk, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, mul_zero, add_mul, Finset.sum_add_distrib, dotF2,
    Finset.mul_sum, mul_assoc]
  ring

/-- Dropping bit `j` undoes the lift. -/
theorem dropPauli_liftPauli (j : Fin (n + 1)) (u : Fin (n + 1) → ZMod 2) (q : Pauli n) :
    dropPauli j u (liftPauli j u q) = q := by
  ext i
  · simp only [dropPauli, liftPauli, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.insertNth_apply_succAbove]
  · simp only [dropPauli, liftPauli, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, zero_mul, add_zero]

/-- On a Pauli whose X-part `u` reads at bit `j`, lifting after dropping adds `Z_j` times the
Z-type Pauli `Z^{e_j + u}`. -/
private theorem liftPauli_dropPauli {j : Fin (n + 1)} {u : Fin (n + 1) → ZMod 2} (huj : u j = 0)
    {q : Pauli (n + 1)} (hq : dotF2 u q.X = q.X j) :
    liftPauli j u (dropPauli j u q) = q + q.Z j • zPauli (Pi.single j 1 + u) := by
  rw [dotF2_succAbove j, huj, zero_mul, zero_add] at hq
  ext k
  · obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
    · simp [liftPauli, dropPauli, zPauli, hq]
    · simp [liftPauli, dropPauli, zPauli]
  · obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
    · simp [liftPauli, dropPauli, zPauli, huj, CharTwo.add_self_eq_zero]
    · simp [liftPauli, dropPauli, zPauli, Fin.succAbove_ne]

/-- The Z-type Pauli `Z^{e_j + u}` commutes with every element of `L` when `u` reads bit `j`. -/
private theorem omega_zPauli_readsBit {j : Fin (n + 1)} {u : Fin (n + 1) → ZMod 2}
    {S : KernelSumState (n + 1)} (hu : ReadsBit (Submodule.map xProj S.L) j u)
    {r : Pauli (n + 1)} (hr : r ∈ S.L) :
    omega r (zPauli (Pi.single j 1 + u)) = 0 := by
  have h := hu.2 _ (Submodule.mem_map_of_mem hr)
  rw [xProj_apply] at h
  rw [omega_comm, omega_zPauli, dotF2_add_left, dotF2_single_left, h]
  exact CharTwo.add_self_eq_zero _

/-- **Dropping a determined bit keeps isotropy**: on `L`, `dropPauli` keeps the symplectic form. -/
theorem isStabilizer_dropPauli {j : Fin (n + 1)} {u : Fin (n + 1) → ZMod 2}
    {S : KernelSumState (n + 1)} (hu : ReadsBit (Submodule.map xProj S.L) j u)
    (hiso : IsStabilizer S.L) :
    IsStabilizer (Submodule.map (dropPauli j u) S.L) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  have hqX := hu.2 _ (Submodule.mem_map_of_mem hq)
  rw [xProj_apply] at hqX
  rw [omega_dropPauli_left, liftPauli_dropPauli hu.1 hqX, omega_add_right, omega_smul_right,
    omega_zPauli_readsBit hu hp, mul_zero, add_zero]
  exact hiso p hp q hq

/-- **Dropping a bit keeps co-isotropy**, for every reader: an element orthogonal to the dropped
Lagrangian lifts to one orthogonal to `L`, which lies in `L`, and dropping undoes the lift. -/
theorem orthogonal_dropPauli_le {j : Fin (n + 1)} {u : Fin (n + 1) → ZMod 2}
    {S : KernelSumState (n + 1)}
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) :
    LinearMap.BilinForm.orthogonal omegaBilin (Submodule.map (dropPauli j u) S.L)
      ≤ Submodule.map (dropPauli j u) S.L := by
  intro q hq
  have hqr : ∀ r ∈ Submodule.map (dropPauli j u) S.L, omega r q = 0 := fun r hr => hq r hr
  have hlift : liftPauli j u q ∈ S.L := by
    refine horth (fun r hr => ?_)
    change omega r (liftPauli j u q) = 0
    rw [← omega_dropPauli_left]
    exact hqr _ (Submodule.mem_map_of_mem hr)
  rw [← dropPauli_liftPauli j u q]
  exact Submodule.mem_map_of_mem hlift

/-- **The amplitude of dropping a determined free bit.** When the support determines bit `j`
(`e_j ∉ π_X(L)`), the amplitude at `w` is the input's at the one extension of `w` on the support,
written as the sum over the two extensions `insertNth j β w`, at most one of which is on the
support. At any height. Proved at T10.3.3. -/
theorem amp_dropFreeBit (j : Fin (n + 1)) (S : KernelSumState (n + 1))
    (hj : (Pi.single j 1 : Fin (n + 1) → ZMod 2) ∉ Submodule.map xProj S.L) :
    amp (dropFreeBit j S)
      = fun w => ∑ β : ZMod 2, amp S (Fin.insertNth j β w : Fin (n + 1) → ZMod 2) := by
  have hu := readsBit_epsilon hj
  funext w
  unfold dropFreeBit
  rw [amp_dropFreeBitBy hu, sum_zmod_two_from _ (dropValue j _ S.x₀ w)]
  have hoff : amp S (Fin.insertNth j (dropValue j
      (Classical.epsilon (ReadsBit (Submodule.map xProj S.L) j)) S.x₀ w + 1) w) = 0 := by
    refine amp_neg (fun hv => ?_)
    have h := eq_dropValue_of_mem_support hu hv
    generalize dropValue j _ S.x₀ w = a at h
    revert a
    decide
  rw [hoff, add_zero]

/-- **Dropping a determined free bit keeps the carrier property.** Proved at T10.3.3. -/
theorem isCarrier_dropFreeBit (j : Fin (n + 1)) {S : KernelSumState (n + 1)} (hS : IsCarrier S)
    (hj : (Pi.single j 1 : Fin (n + 1) → ZMod 2) ∉ Submodule.map xProj S.L) :
    IsCarrier (dropFreeBit j S) := by
  have hu := readsBit_epsilon hj
  obtain ⟨hm, hiso, horth, hne⟩ := hS
  refine ⟨hm, isStabilizer_dropPauli hu hiso, orthogonal_dropPauli_le horth, fun h0 => hne ?_⟩
  funext v
  by_cases hv : ∃ p ∈ S.L, v = S.x₀ + p.X
  · have hon : ∃ p ∈ S.L, (Fin.insertNth j (v j) (Fin.removeNth j v) : Fin (n + 1) → ZMod 2)
        = S.x₀ + p.X := by
      rw [Fin.insertNth_self_removeNth]
      exact hv
    have hval := eq_dropValue_of_mem_support hu hon
    have hw := congrFun h0 (Fin.removeNth j v)
    unfold dropFreeBit at hw
    rw [amp_dropFreeBitBy hu, ← hval, Fin.insertNth_self_removeNth] at hw
    exact hw
  · exact amp_neg hv

/-- The outcome label of conditioning on `P` at outcome `b`: the factor `(−1)^b·(−1)^{sign}` that
the projection `½(1 + (−1)^b P)` puts on `P`'s Hermitian Pauli. Its frame form is `outcomeChi`. -/
noncomputable def outcomeSign (P : SignedPauli n) (b : ZMod 2) : ℂ :=
  (-1 : ℂ) ^ b.val * (-1 : ℂ) ^ P.sign.val

/-- The outcome label squares to one. -/
theorem outcomeSign_mul_self (P : SignedPauli n) (b : ZMod 2) :
    outcomeSign P b * outcomeSign P b = 1 := by
  unfold outcomeSign
  calc (-1 : ℂ) ^ b.val * (-1 : ℂ) ^ P.sign.val * ((-1 : ℂ) ^ b.val * (-1 : ℂ) ^ P.sign.val)
      = ((-1 : ℂ) * -1) ^ b.val * ((-1 : ℂ) * -1) ^ P.sign.val := by
        rw [mul_pow, mul_pow]
        ring
    _ = 1 := by norm_num

/-- A Pauli with `ω = 0` against `P` commutes with the projection on `P`. -/
theorem pauliAct_pauliProjection {g : Pauli n} {P : SignedPauli n} (h : omega g P.pauli = 0)
    (b : ZMod 2) (f : (Fin n → ZMod 2) → ℂ) :
    pauliAct g (pauliProjection P b f) = pauliProjection P b (pauliAct g f) := by
  funext w
  unfold pauliProjection SignedPauli.act
  rw [← pauliAct_comm h f]
  simp only [pauliAct]
  ring

/-- The projection commutes with a constant factor. -/
theorem pauliProjection_mul_left (P : SignedPauli n) (b : ZMod 2) (c : ℂ)
    (f : (Fin n → ZMod 2) → ℂ) :
    pauliProjection P b (fun w => c * f w) = fun w => c * pauliProjection P b f w := by
  funext w
  simp only [pauliProjection, SignedPauli.act, pauliAct_mul_left]
  ring

/-- `P` acts on its projection as the outcome label. -/
theorem pauliAct_self_pauliProjection (P : SignedPauli n) (b : ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) :
    pauliAct P.pauli (pauliProjection P b f)
      = fun w => outcomeSign P b * pauliProjection P b f w := by
  have hlin : pauliProjection P b f
      = fun w => (1 / 2 : ℂ) * f w + (1 / 2 * outcomeSign P b) * pauliAct P.pauli f w := by
    funext w
    simp only [pauliProjection, SignedPauli.act, outcomeSign]
    ring
  have hact : ∀ (a c : ℂ) (u v : (Fin n → ZMod 2) → ℂ),
      pauliAct P.pauli (fun w => a * u w + c * v w)
        = fun w => a * pauliAct P.pauli u w + c * pauliAct P.pauli v w := by
    intro a c u v
    funext w
    simp only [pauliAct]
    ring
  rw [hlin, hact, pauliAct_pauliAct]
  funext w
  linear_combination (-(1 / 2) * pauliAct P.pauli f w) * outcomeSign_mul_self P b

/-- **The conditioned amplitude is stabilized by `pauliCondition L P`.** Elements of `L` that
commute with `P` commute with the projection, and `P` acts on it as the outcome label. -/
theorem stabilizedBy_pauliCondition {L : Submodule (ZMod 2) (Pauli n)}
    (hL : IsStabilizer L) {f : (Fin n → ZMod 2) → ℂ} (hs : StabilizedBy L f) (P : SignedPauli n)
    (b : ZMod 2) (hf : pauliProjection P b f ≠ 0) :
    StabilizedBy (pauliCondition L P.pauli) (pauliProjection P b f) := by
  have hcomm : ∀ g ∈ L, omega g P.pauli = 0 →
      ∃ s : ZMod 2, pauliAct g (pauliProjection P b f)
        = fun w => (-1 : ℂ) ^ s.val * pauliProjection P b f w := by
    intro g hg hgP
    obtain ⟨s, hsg⟩ := hs g hg
    exact ⟨s, by rw [pauliAct_pauliProjection hgP, hsg, pauliProjection_mul_left]⟩
  have hself : ∃ s : ZMod 2, pauliAct P.pauli (pauliProjection P b f)
      = fun w => (-1 : ℂ) ^ s.val * pauliProjection P b f w :=
    exists_sign_of_pauliAct_eq hf (pauliAct_self_pauliProjection P b f)
  by_cases hPL : P.pauli ∈ L
  · rw [pauliCondition_of_mem hPL]
    intro g hg
    exact hcomm g hg (hL g hg P.pauli hPL)
  · rw [pauliCondition_of_not_mem hPL]
    refine stabilizedBy_sup hf ?_ ?_
    · intro g hg
      obtain ⟨hgL, hgo⟩ := Submodule.mem_inf.mp hg
      have hPg : omega P.pauli g = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hgo) P.pauli
          (Submodule.mem_span_singleton_self _)
      exact hcomm g hgL (by rw [omega_comm]; exact hPg)
    · intro g hg
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
      rcases zmod_two_eq_zero_or_one a with rfl | rfl
      · refine ⟨0, ?_⟩
        rw [zero_smul, pauliAct_zero]
        funext w
        rw [ZMod.val_zero, pow_zero, one_mul]
      · rw [one_smul]
        exact hself

/-- The Pauli with its sign moves the value at `w + X` to `w` and multiplies it by a unit, so its
squared norm is the one at `w + X`. -/
theorem normSq_act (P : SignedPauli n) (f : (Fin n → ZMod 2) → ℂ) (w : Fin n → ZMod 2) :
    Complex.normSq (P.act f w) = Complex.normSq (f (w + P.pauli.X)) := by
  simp only [SignedPauli.act, pauliAct, map_mul, map_pow, Complex.normSq_neg, Complex.normSq_one,
    Complex.normSq_I, one_pow, one_mul]

/-- The Pauli with its sign keeps the sum of squared norms: it is a unit factor times a shift, and
the shift by `X` is a bijection of the words. -/
theorem sum_normSq_act (P : SignedPauli n) (f : (Fin n → ZMod 2) → ℂ) :
    ∑ w : Fin n → ZMod 2, Complex.normSq (P.act f w)
      = ∑ w : Fin n → ZMod 2, Complex.normSq (f w) := by
  simp only [normSq_act]
  exact Fintype.sum_equiv (Equiv.addRight P.pauli.X) _ _ (fun _ => rfl)

/-- The Hermitian Pauli action keeps the sum of squared norms. -/
theorem sum_normSq_pauliAct (g : Pauli n) (f : (Fin n → ZMod 2) → ℂ) :
    ∑ w : Fin n → ZMod 2, Complex.normSq (pauliAct g f w)
      = ∑ w : Fin n → ZMod 2, Complex.normSq (f w) := by
  have h := sum_normSq_act ⟨0, g⟩ f
  simpa only [SignedPauli.act, ZMod.val_zero, pow_zero, one_mul] using h

/-- Raising the outcome flips its sign: `(−1)^{(b+1)} = −(−1)^b`. -/
theorem neg_one_pow_val_add_one (b : ZMod 2) :
    (-1 : ℂ) ^ (b + 1).val = -(-1 : ℂ) ^ b.val := by
  fin_cases b
  · show (-1 : ℂ) ^ (1 : ℕ) = -(-1 : ℂ) ^ (0 : ℕ)
    simp only [pow_one, pow_zero]
  · show (-1 : ℂ) ^ (0 : ℕ) = -(-1 : ℂ) ^ (1 : ℕ)
    simp only [pow_one, pow_zero, neg_neg]

end FTQCLib.Frame.Walkthrough

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.FrameCategory
import FTQCLib.Cohomology.PauliExtension

/-!
# Pauli errors on carrier states

An error is an element `P = ⟨e, p⟩` of the Pauli group `PauliGroup n`
(`Cohomology/PauliExtension.lean`): a phase `e : ZMod 4`, the power of `i`, and a register element
`p = (a, z) : Pauli n`, its X-part `a` and its Z-part `z`. It acts on amplitude functions by
`PauliGroup.act P f = i^e·pauliAct p f` (`docs/TARGETS.md`, T64), where `pauliAct` is the Hermitian
Pauli `f ↦ (w ↦ i^{yWeight p}·(−1)^{z·(w + a)}·f(w + a))`. A Pauli with its sign, `SignedPauli n`,
is the element `⟨2·sign, p⟩` (`SignedPauli.toPauliGroup`), on which `act` is `SignedPauli.act`
(`act_toPauliGroup`); its image is the elements of even phase and is not closed under the product.

**The move.** `applyPauli P S` acts on a carrier record `⟨m, h, Q, c, L, x₀⟩`: the support moves to
`x₀ + a` with `L` unchanged, the exponent becomes `Q(w + a, y) + 2^{k−1}·z·(w + a) + 2^{k−2}·(e +
yWeight p)` (the last term written exactly at every precision by `iPowExp`), and the height and
the scale are unchanged. The precision `k` is `pauliPrecision S.m P`: the input's, raised to `1`,
and to `2` where `e + yWeight p` is odd, as `conditionPrecision` raises it for conditioning; the
exponent is lifted to it by R7 (`liftTo`). Its referee (decision D5) is `amp_applyPauli`:
`amp (applyPauli P S) = P.act (amp S)`, on every record. On a carrier state it keeps the carrier
property and the height (`isCarrier_applyPauli`), and it is `StateEq` to the run of the gate word
`pauliWord P` (`applyPauli_stateEq_pauliWord`): one diagonal letter for the Z-part and the phase,
then each X as H, the diagonal letter `2^{m−1}·w_j`, H.

**Composition** is the product in the order of application: `y.act (x.act f) = (x * y).act f`
(`PauliGroup.act_act`), by `pauliAct_add`. So `act` is a right action, and `X * Z` in
`PauliGroup` is `⟨1, Y⟩`, which acts as the matrix `ZX = iY`; the matrix product `XZ` is `−iY`.

**Protocols.** `Protocol.append p q` runs `q : Protocol m (n + k) k'` on the `n + k` free bits that
`p : Protocol m n k` ends on, its letters cast along `n + k + k' = n + (k + k')`
(`interpret_append`). A **location** of a protocol (`Protocol.Location`) is a gap between two of
its letters, the letters of each word counted one by one: the start of the empty protocol, a
location of `p` in `p.word w` (before `w`), the gap after the `i`-th letter of `w`, a location of
`p` in `p.condition P hP`, and the gap just after that conditioning letter. Each location is a
split: `ℓ.before` and `ℓ.after`, with `ℓ.outcomes` outcome bits before it and `ℓ.rest` after it,
and `Protocol.insertAt p ℓ w` is `ℓ.before`, then the one-word protocol `nil.word w`, then
`ℓ.after` (`interpret_insertAt`; with `w = []` it says that `p` is its split up to
interpretation). A **fault set** (`FaultSet`) is a Pauli at every location, the identity where
there is no fault, and `Protocol.faulty p F` places every one of them. A **measurement error** is X
on an outcome bit just after its conditioning letter (`Protocol.measurementError`).

**Outcome-controlled errors.** For `d : (Fin r → ZMod 2) → PauliGroup n`, `outcomePauliWord d` on
the `n + r` free bits, the last `r` of them outcome bits, applies `d(s)` at outcome string `s`
(`runAmp_outcomePauliWord`): one diagonal letter `2^{m−1}·Σ_j d^Z_j(s)·w_j` plus the phase
`2^{m−2}·(e(s) + yWeight(d(s).base))`, then for each data bit `j` the letters H, `2^{m−1}·d^X_j(s)
·w_j`, H. Each function of the outcome bits is written as its indicator expansion
(`outcomePoly`), which equals it at every outcome string; the target's text writes
`yWeight(d(s).base)` as the polynomial `Σ_j d^X_j(s)·d^Z_j(s)`, the same function. The precision
must be at least `2` where some `e(s) + yWeight(d(s).base)` is odd. T13's `controlledPauliWord` is
the case of one outcome bit in referee, not in letters: it shifts by CNOTs and has no H letter.

Everything here is frame-pure (decision D5): no `FTQCLib.Hilbert` module is imported.

## Main definitions

* `PauliGroup.act`, `SignedPauli.toPauliGroup` — the action of the Pauli group on amplitude
  functions, and the map from Paulis with their sign.
* `pauliPrecision`, `pauliErrorPhase`, `applyPauli` — the move on carrier records.
* `pauliWord` — the gate word of a Pauli group element.
* `Protocol.append`, `Protocol.Location`, `Protocol.insertAt`, `Protocol.FaultSet`,
  `Protocol.faulty`, `Protocol.measurementError` — concatenation, locations and faults.
* `outcomePoly`, `outcomePauliWord` — a Pauli chosen by outcome bits, as a word.

## Main results

* `amp_applyPauli` — the move's amplitude is `P.act` of the input's.
* `isCarrier_applyPauli` — on a carrier state, carrier property and height kept.
* `applyPauli_stateEq_pauliWord` — the move is `StateEq` to the run of `pauliWord P`.
* `PauliGroup.act_act` — composition is the product in the order of application.
* `interpret_append`, `interpret_insertAt` — the interpretation of a concatenation and of an
  inserted word.
* `runAmp_outcomePauliWord` — at every outcome string `s`, the run applies `d(s)`.

## Implementation notes

* The Z-phase is added before the translation, so it reads `z·(w + a)` and the scale is
  `i^{e + yWeight}` (`docs/fidelity/T64.md`, condition 2); adding `z·w` after it would need
  `i^{e + 3·yWeight}`.
* Locations are gaps between single letters, so a split inside a word is a location; the split is
  then equal to the protocol up to interpretation (`run_append`), not as a term.
* A fault set gives a Pauli at every location, so it is a function on the locations; a location
  without a fault carries the identity, whose word is one diagonal letter with phase `0`.

## References

* D. Gottesman, *Stabilizer codes and quantum error correction*, arXiv:quant-ph/9705052: the Pauli
  group, `Y = iXZ`, and `H Z H = X`; cited unit by unit above the declarations below. Its group is
  the group of matrices under the matrix product; here the product is in the order of application,
  the opposite group, and an element is written by its phase and its binary form.
-/

namespace FTQCLib.Cohomology.PauliGroup

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer

variable {n : ℕ}

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h200c97f6540a
/-- **The action of a Pauli group element** on an amplitude function: `i^e` times the Hermitian
Pauli `pauliAct` of its register element, `w ↦ i^{e + yWeight p}·(−1)^{z·(w + a)}·f(w + a)`. -/
noncomputable def act (P : PauliGroup n) (f : (Fin n → ZMod 2) → ℂ) : (Fin n → ZMod 2) → ℂ :=
  fun w => Complex.I ^ P.phase.val * pauliAct P.base f w

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 equation:h89f913675a15
/-- **Composition is the product in the order of application**: `x`, then `y`, is `x * y`. So
`act` is a right action, and `⟨0, X⟩ * ⟨0, Z⟩ = ⟨1, Y⟩` acts as the matrix `ZX = iY`, where the
source's matrix product `XZ` is `−iY`. Proved at a later step. -/
theorem act_act (x y : PauliGroup n) (f : (Fin n → ZMod 2) → ℂ) :
    y.act (x.act f) = (x * y).act f := by
  funext w
  have hcomp := congrFun (pauliAct_add y.base x.base f) w
  change Complex.I ^ y.phase.val
        * pauliAct y.base (fun v => Complex.I ^ x.phase.val * pauliAct x.base f v) w
      = Complex.I ^ (x * y).phase.val * pauliAct (x * y).base f w
  rw [pauliAct_mul_left]
  beta_reduce
  rw [hcomp, mul_phase, mul_base, I_pow_val_add, I_pow_val_add, add_comm x.base y.base]
  ring

end FTQCLib.Cohomology.PauliGroup

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer FTQCLib.Cohomology

variable {n : ℕ}

/-! ## Paulis with their sign -/

/-- **A Pauli with its sign as a Pauli group element**: `⟨2·sign, pauli⟩`, the phase `i^{2·sign} =
(−1)^sign`. -/
def SignedPauli.toPauliGroup (P : SignedPauli n) : PauliGroup n :=
  ⟨2 * (P.sign.val : ZMod 4), P.pauli⟩

/-- On a Pauli with its sign, the Pauli group's action is `SignedPauli.act`. -/
theorem act_toPauliGroup (P : SignedPauli n) : P.toPauliGroup.act = P.act := by
  rcases P with ⟨s, p⟩
  funext f w
  simp only [PauliGroup.act, SignedPauli.act, SignedPauli.toPauliGroup]
  congr 1
  rcases ((show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) s) with rfl | rfl
  · rw [show ((2 : ZMod 4) * (((0 : ZMod 2).val : ℕ) : ZMod 4)).val = 0 from rfl,
      show (0 : ZMod 2).val = 0 from rfl, pow_zero, pow_zero]
  · rw [show ((2 : ZMod 4) * (((1 : ZMod 2).val : ℕ) : ZMod 4)).val = 2 from rfl,
      show (1 : ZMod 2).val = 1 from rfl, Complex.I_sq, pow_one]

/-! ## The move on carrier records -/

/-- The precision the move works at: the input's, raised to `1` for the sign and to `2` where
`e + yWeight` is odd, for the factor `i^{e + yWeight}`. -/
def pauliPrecision (m : ℕ) (P : PauliGroup n) : ℕ :=
  if (P.phase.val + yWeight P.base) % 2 = 0 then max m 1 else max m 2

/-- The input's precision is at most the move's: the lift is R7. -/
theorem le_pauliPrecision (m : ℕ) (P : PauliGroup n) : m ≤ pauliPrecision m P := by
  unfold pauliPrecision
  split
  · exact le_max_left m 1
  · exact le_max_left m 2

/-- The move's precision is positive. -/
theorem one_le_pauliPrecision (m : ℕ) (P : PauliGroup n) : 1 ≤ pauliPrecision m P := by
  unfold pauliPrecision
  split
  · exact le_max_right m 1
  · exact le_trans (by norm_num) (le_max_right m 2)

/-- The exponent, at precision `k`, of the factor `P` puts on the value at the translated word:
`2^{k−1}·Σ_j z_j·(w_j + t_j) + 2^{k−2}·(e + yWeight)`, the free variable `j` read at `ι j`. With
`t` the X-part it is `(−1)^{z·(w + a)}·i^{e + yWeight}`; with `t = 0`, `(−1)^{z·w}·i^{e + yWeight}`.
The sum `w_j + t_j` is of the bits' values, read only under the top bit `2^{k−1}`. -/
noncomputable def pauliErrorPhase {N : ℕ} (k : ℕ) (ι : Fin n → Fin N) (P : PauliGroup n)
    (t : Fin n → ZMod 2) : DiagPhase N k :=
  MvPolynomial.C ((2 : ZMod (2 ^ k)) ^ (k - 1))
      * ∑ j : Fin n, MvPolynomial.C (((P.base.Z j).val : ZMod (2 ^ k)))
          * (MvPolynomial.X (ι j) + MvPolynomial.C (((t j).val : ZMod (2 ^ k))))
    + MvPolynomial.C (iPowExp k (P.phase.val + yWeight P.base))

/-- **A Pauli group element applied to a carrier record.** At the precision `pauliPrecision`: the
exponent lifted by R7 and precomposed with the translation `w ↦ w + a` of the free bits, plus the
phase `pauliErrorPhase` at the X-part; the support's offset moved to `x₀ + a`; the height, the
scale and the Lagrangian unchanged. -/
noncomputable def applyPauli (P : PauliGroup n) (S : KernelSumState n) : KernelSumState n where
  m := pauliPrecision S.m P
  h := S.h
  Q := shiftSubst id P.base.X 1
        (FTQCLib.Hilbert.liftTo (pauliPrecision S.m P) (le_pauliPrecision S.m P) S.Q)
      + pauliErrorPhase (pauliPrecision S.m P) (Fin.castAdd S.h) P P.base.X
  c := S.c
  L := S.L
  x₀ := S.x₀ + P.base.X

@[simp] theorem applyPauli_m (P : PauliGroup n) (S : KernelSumState n) :
    (applyPauli P S).m = pauliPrecision S.m P :=
  rfl

@[simp] theorem applyPauli_h (P : PauliGroup n) (S : KernelSumState n) :
    (applyPauli P S).h = S.h :=
  rfl

/-- Where `e + yWeight` is odd the move's precision is at least `2`. -/
private theorem two_le_pauliPrecision {m : ℕ} {P : PauliGroup n}
    (hodd : (P.phase.val + yWeight P.base) % 2 = 1) : 2 ≤ pauliPrecision m P := by
  unfold pauliPrecision
  rw [if_neg (by omega)]
  exact le_max_right m 2

/-- Adding a word twice adds nothing: the words are over `𝔽₂`. -/
private theorem add_add_self_bits {N : ℕ} (u a : Fin N → ZMod 2) : u + a + a = u := by
  funext i
  exact (show ∀ x y : ZMod 2, x + y + y = x by decide) (u i) (a i)

/-- The signs of the Z-part at the translated word: the sum of the bits' values and their sum in
`𝔽₂` have the same parity. -/
private theorem neg_one_pow_sum_val_add (p : Pauli n) (w a : Fin n → ZMod 2) :
    (-1 : ℂ) ^ (∑ j : Fin n, (p.Z j).val * ((w j).val + (a j).val)) = (-1) ^ zDot p (w + a) := by
  apply neg_one_pow_eq_of_cast_eq
  rw [zDot_cast_two]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id, Pi.add_apply]

/-- The character of `pauliErrorPhase` at a positive precision, `2` or more where `e + yWeight` is
odd: the sign of the Z-part at the word read through `ι` and translated by `t`, times
`i^{e + yWeight}`. -/
private theorem charOf_pauliErrorPhase_eval {N k : ℕ} (hk : 1 ≤ k) (ι : Fin n → Fin N)
    (P : PauliGroup n) (t : Fin n → ZMod 2)
    (hodd : (P.phase.val + yWeight P.base) % 2 = 1 → 2 ≤ k) (v : Fin N → ZMod 2) :
    charOf k ((pauliErrorPhase k ι P t).eval v)
      = (-1) ^ zDot P.base ((fun j => v (ι j)) + t)
        * Complex.I ^ (P.phase.val + yWeight P.base) := by
  have hsum : DiagPhase.eval
      (∑ j : Fin n, MvPolynomial.C (((P.base.Z j).val : ZMod (2 ^ k)))
        * (MvPolynomial.X (ι j) + MvPolynomial.C (((t j).val : ZMod (2 ^ k))))) v
      = ((∑ j : Fin n, (P.base.Z j).val * ((v (ι j)).val + (t j).val) : ℕ) : ZMod (2 ^ k)) := by
    simp only [DiagPhase.eval, map_sum, map_mul, map_add, MvPolynomial.eval_C,
      MvPolynomial.eval_X, DiagPhase.liftBinary]
    push_cast
    rfl
  unfold pauliErrorPhase
  rw [DiagPhase.eval_add, charOf_add, DiagPhase.eval_C, charOf_iPowExp _ hk hodd,
    DiagPhase.eval_mul, DiagPhase.eval_C, hsum, charOf_two_pow_mul hk,
    neg_one_pow_sum_val_add P.base (fun j => v (ι j)) t]

/-- The move's exponent at `w ++ y`: the input's at `(w + a) ++ y` plus the factor's. -/
private theorem charOf_eval_applyPauli_append (P : PauliGroup n) (S : KernelSumState n)
    (w : Fin n → ZMod 2) (y : Fin S.h → ZMod 2) :
    charOf (applyPauli P S).m ((applyPauli P S).Q.eval (Fin.append w y))
      = charOf S.m (S.Q.eval (Fin.append (w + P.base.X) y))
        * ((-1) ^ zDot P.base (w + P.base.X) * Complex.I ^ (P.phase.val + yWeight P.base)) := by
  have hT : (1 : DiagPhase (n + S.h) (pauliPrecision S.m P)).eval (Fin.append w y)
      = (((1 : ZMod 2).val : ℕ) : ZMod (2 ^ pauliPrecision S.m P)) := by
    rw [show ((1 : ZMod 2).val) = 1 from rfl, Nat.cast_one]
    exact map_one _
  change charOf (pauliPrecision S.m P)
      ((shiftSubst id P.base.X 1
          (FTQCLib.Hilbert.liftTo (pauliPrecision S.m P) (le_pauliPrecision S.m P) S.Q)
        + pauliErrorPhase (pauliPrecision S.m P) (Fin.castAdd S.h) P P.base.X).eval
          (Fin.append w y)) = _
  rw [DiagPhase.eval_add, charOf_add, shiftSubst_eval id P.base.X 1 _ _ 1 hT, charOf_eval_liftTo,
    charOf_pauliErrorPhase_eval (one_le_pauliPrecision S.m P) _ P P.base.X
      (fun h => two_le_pauliPrecision h)]
  have hshift : (fun l => Fin.append w y (id l) + 1 * Fin.append P.base.X (0 : Fin S.h → ZMod 2) l)
      = Fin.append (w + P.base.X) y := by
    funext l
    refine Fin.addCases (fun i => ?_) (fun j => ?_) l
    · simp only [id, one_mul, Fin.append_left, Pi.add_apply]
    · simp only [id, one_mul, Fin.append_right, Pi.zero_apply, add_zero]
  have hread : (fun j => Fin.append w y (Fin.castAdd S.h j)) = w := by
    funext j
    exact Fin.append_left w y j
  rw [hshift, hread]

/-- **The move on support**: its on-support amplitude at `w` is the factor times the input's at
`w + a`. -/
private theorem ampCore_applyPauli (P : PauliGroup n) (S : KernelSumState n)
    (w : Fin n → ZMod 2) :
    ampCore (applyPauli P S).m (applyPauli P S).h (applyPauli P S).Q (applyPauli P S).c w
      = (-1) ^ zDot P.base (w + P.base.X) * Complex.I ^ (P.phase.val + yWeight P.base)
        * ampCore S.m S.h S.Q S.c (w + P.base.X) := by
  change S.c / (Real.sqrt 2 : ℂ) ^ S.h * ∑ y : Fin S.h → ZMod 2,
      charOf (applyPauli P S).m ((applyPauli P S).Q.eval (Fin.append w y))
    = _ * (S.c / (Real.sqrt 2 : ℂ) ^ S.h * ∑ y : Fin S.h → ZMod 2,
      charOf S.m (S.Q.eval (Fin.append (w + P.base.X) y)))
  rw [Finset.sum_congr rfl fun y _ => charOf_eval_applyPauli_append P S w y, ← Finset.sum_mul]
  ring

/-- The move's support is the input's, translated by `a`. -/
private theorem mem_support_applyPauli_iff (P : PauliGroup n) (S : KernelSumState n)
    (w : Fin n → ZMod 2) :
    (∃ p ∈ (applyPauli P S).L, w = (applyPauli P S).x₀ + p.X)
      ↔ (∃ p ∈ S.L, w + P.base.X = S.x₀ + p.X) := by
  constructor
  · rintro ⟨p, hp, hw⟩
    refine ⟨p, hp, ?_⟩
    change w = S.x₀ + P.base.X + p.X at hw
    rw [hw, add_right_comm S.x₀ P.base.X p.X, add_add_self_bits]
  · rintro ⟨p, hp, hw⟩
    refine ⟨p, hp, ?_⟩
    change w = S.x₀ + P.base.X + p.X
    rw [← add_add_self_bits w P.base.X, hw, add_right_comm S.x₀ p.X P.base.X]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h638c779e61d3
/-- **The referee of the move** (decision D5): its amplitude is `P.act` of the input's, on every
record. Proved at a later step. -/
theorem amp_applyPauli (P : PauliGroup n) (S : KernelSumState n) :
    amp (applyPauli P S) = P.act (amp S) := by
  funext w
  change _ = Complex.I ^ P.phase.val * (Complex.I ^ yWeight P.base
    * (-1) ^ zDot P.base (w + P.base.X) * amp S (w + P.base.X))
  by_cases hw : ∃ p ∈ S.L, w + P.base.X = S.x₀ + p.X
  · rw [amp_pos ((mem_support_applyPauli_iff P S w).mpr hw), ampCore_applyPauli, amp_pos hw,
      pow_add]
    ring
  · rw [amp_neg (fun h => hw ((mem_support_applyPauli_iff P S w).mp h)), amp_neg hw]
    ring

/-- **The move keeps the carrier property and the height**: the precision is positive, the
Lagrangian is the same, the amplitude is nonzero since `act` is injective, and no summation
variable is added. Proved at a later step. -/
theorem isCarrier_applyPauli (P : PauliGroup n) {S : KernelSumState n} (hS : IsCarrier S) :
    IsCarrier (applyPauli P S) ∧ (applyPauli P S).h = S.h := by
  refine ⟨⟨one_le_pauliPrecision S.m P, hS.2.1, hS.2.2.1, fun hzero => hS.2.2.2 ?_⟩, rfl⟩
  rw [amp_applyPauli] at hzero
  have hpauli : pauliAct P.base (amp S) = 0 := by
    funext w
    have hw := congrFun hzero w
    change Complex.I ^ P.phase.val * pauliAct P.base (amp S) w = 0 at hw
    exact (mul_eq_zero.mp hw).resolve_left (pow_ne_zero _ Complex.I_ne_zero)
  exact (pauliAct_eq_zero_iff P.base (amp S)).mp hpauli

/-! ## The gate word -/

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 equation:he6e827075ed8
/-- **The gate word of a Pauli group element** at precision `m`: the diagonal letter of the Z-part
and the phase, `2^{m−1}·z·w + 2^{m−2}·(e + yWeight)`, then, for each bit `j` of the X-part, X as
`H Z H`: H on `j`, the diagonal letter `2^{m−1}·w_j`, H on `j`. The Z-part acts first. -/
noncomputable def pauliWord {m : ℕ} (P : PauliGroup n) : GateWord n m :=
  GateLetter.diagonal (pauliErrorPhase m id P 0)
    :: (List.finRange n).flatMap fun j =>
      if P.base.X j = 1 then
        [GateLetter.hadamard j,
          GateLetter.diagonal (MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * MvPolynomial.X j),
          GateLetter.hadamard j]
      else []

/-- Every bit is `0` or `1`. -/
private theorem bit_cases_pauliWord (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/-- The translation by `e_j` is the update of bit `j` to its flip. -/
private theorem update_flip_eq_add_single_bits {N : ℕ} (w : Fin N → ZMod 2) (j : Fin N) :
    Function.update w j (w j + 1) = w + Pi.single j 1 := by
  funext l
  by_cases hl : l = j
  · subst hl
    rw [Function.update_self, Pi.add_apply, Pi.single_eq_same]
  · rw [Function.update_of_ne hl, Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 equation:he6e827075ed8
/-- **H, a controlled sign, H is the controlled X**: on bit `j`, with a diagonal letter whose
character is `(−1)^{c(w)·w_j}` for a bit function `c` that does not read bit `j`, the three
letters translate by `c(w)·e_j`. -/
private theorem runAmp_hadamardSandwich {N m : ℕ} (j : Fin N) (D : DiagPhase N m)
    (c : (Fin N → ZMod 2) → ZMod 2)
    (hD : ∀ w, charOf m (D.eval w) = (-1) ^ ((c w).val * (w j).val))
    (hc : ∀ w b, c (Function.update w j b) = c w) (f : (Fin N → ZMod 2) → ℂ) :
    runAmp ([GateLetter.hadamard j, GateLetter.diagonal D, GateLetter.hadamard j] :
        GateWord N m) f
      = fun w => f (w + c w • (Pi.single j 1 : Fin N → ZMod 2)) := by
  funext w
  have h2 : (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs0 : signOf (0 : ZMod 2) = 1 := signOf_zero
  have hs1 : signOf (1 : ZMod 2) = -1 := signOf_one
  simp only [runAmp_cons, runAmp_nil, letterAmp, walshTransform, Function.update_idem,
    Function.update_self, hD, hc, hs0, hs1, ZMod.val_zero, ZMod.val_one, mul_zero, mul_one,
    pow_zero, one_mul]
  rcases bit_cases_pauliWord (c w) with hcw | hcw <;>
    rcases bit_cases_pauliWord (w j) with hwj | hwj
  · have hw : Function.update w j 0 = w := by rw [← hwj]; exact Function.update_eq_self j w
    rw [hcw, hwj, hs0, hw, zero_smul, add_zero]
    simp only [ZMod.val_zero, pow_zero, one_mul]
    linear_combination (2 * f w) * h2
  · have hw : Function.update w j 1 = w := by rw [← hwj]; exact Function.update_eq_self j w
    rw [hcw, hwj, hs1, hw, zero_smul, add_zero]
    simp only [ZMod.val_zero, pow_zero, one_mul]
    linear_combination (2 * f w) * h2
  · have hflip : w + Pi.single j 1 = Function.update w j 1 := by
      rw [← update_flip_eq_add_single_bits, hwj, zero_add]
    rw [hcw, hwj, hs0, one_smul, hflip]
    simp only [ZMod.val_one, pow_one]
    linear_combination (2 * f (Function.update w j 1)) * h2
  · have hflip : w + Pi.single j 1 = Function.update w j 0 := by
      rw [← update_flip_eq_add_single_bits, hwj]
      rfl
    rw [hcw, hwj, hs1, one_smul, hflip]
    simp only [ZMod.val_one, pow_one]
    linear_combination (2 * f (Function.update w j 0)) * h2

/-- **Words that translate, run one after another**: if each word `W x` translates by `t x w`, a
vector in `V`, and `t x` does not change under a translation by `V`, the concatenation translates
by the sum. -/
private theorem runAmp_flatMap_translate {N m : ℕ} {α : Type*}
    (V : Submodule (ZMod 2) (Fin N → ZMod 2)) (W : α → GateWord N m)
    (t : α → (Fin N → ZMod 2) → (Fin N → ZMod 2)) (l : List α)
    (ht : ∀ x ∈ l, ∀ w, t x w ∈ V) (hinv : ∀ x ∈ l, ∀ w, ∀ v ∈ V, t x (w + v) = t x w)
    (hW : ∀ x ∈ l, ∀ g, runAmp (W x) g = fun w => g (w + t x w))
    (g : (Fin N → ZMod 2) → ℂ) :
    runAmp (l.flatMap W) g = fun w => g (w + (l.map fun x => t x w).sum) := by
  induction l generalizing g with
  | nil =>
    funext w
    rw [List.flatMap_nil, runAmp_nil, List.map_nil, List.sum_nil, add_zero]
  | cons x l ih =>
    have hx : x ∈ x :: l := List.mem_cons_self
    have hl : ∀ y ∈ l, y ∈ x :: l := fun y hy => List.mem_cons_of_mem x hy
    rw [List.flatMap_cons, runAmp_append, hW x hx g,
      ih (fun y hy => ht y (hl y hy)) (fun y hy => hinv y (hl y hy))
        (fun y hy => hW y (hl y hy))]
    funext w
    have hmem : (l.map fun y => t y w).sum ∈ V := by
      refine list_sum_mem fun v hv => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
      exact ht y (hl y hy) w
    rw [hinv x hx w _ hmem, List.map_cons, List.sum_cons, add_comm (t x w), add_assoc]

/-- The sum of `a_j·e_j` over the bits is `a`. -/
private theorem sum_finRange_smul_single {N : ℕ} (a : Fin N → ZMod 2) :
    ((List.finRange N).map fun j => a j • (Pi.single j 1 : Fin N → ZMod 2)).sum = a := by
  rw [← Fin.sum_univ_def]
  funext l
  rw [Finset.sum_apply, Finset.sum_eq_single l]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h

/-- One bit's letters of `pauliWord`: H, the half turn on the bit, H where the X-part has the bit,
nothing where it does not; either way the translation by `a_j·e_j`. -/
private theorem runAmp_pauliWord_bit {m : ℕ} (P : PauliGroup n) (hm : 1 ≤ m) (j : Fin n)
    (g : (Fin n → ZMod 2) → ℂ) :
    runAmp ((if P.base.X j = 1 then
        [GateLetter.hadamard j,
          GateLetter.diagonal (MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * MvPolynomial.X j),
          GateLetter.hadamard j]
      else []) : GateWord n m) g
      = fun w => g (w + P.base.X j • (Pi.single j 1 : Fin n → ZMod 2)) := by
  by_cases hj : P.base.X j = 1
  · rw [if_pos hj, hj, runAmp_hadamardSandwich j _ (fun _ => 1) ?_ (fun _ _ => rfl) g]
    intro w
    rw [DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X, charOf_two_pow_mul hm,
      ZMod.val_one, one_mul]
  · rw [if_neg hj, runAmp_nil]
    have hj0 : P.base.X j = 0 := (bit_cases_pauliWord _).resolve_right hj
    funext w
    rw [hj0, zero_smul, add_zero]

/-- **The referee of the Pauli's word**: at a positive precision, `2` or more where `e + yWeight`
is odd, the run of `pauliWord P` is `P.act`. -/
private theorem runAmp_pauliWord {m : ℕ} (P : PauliGroup n) (hm : 1 ≤ m)
    (hodd : (P.phase.val + yWeight P.base) % 2 = 1 → 2 ≤ m) (f : (Fin n → ZMod 2) → ℂ) :
    runAmp (pauliWord P : GateWord n m) f = P.act f := by
  unfold pauliWord
  rw [runAmp_cons, runAmp_flatMap_translate ⊤ _
    (fun j (_ : Fin n → ZMod 2) => P.base.X j • (Pi.single j 1 : Fin n → ZMod 2))
    (List.finRange n) (fun _ _ _ => Submodule.mem_top) (fun _ _ _ _ _ => rfl)
    (fun j _ g => runAmp_pauliWord_bit P hm j g)]
  funext w
  rw [sum_finRange_smul_single]
  change charOf m ((pauliErrorPhase m id P 0).eval (w + P.base.X)) * f (w + P.base.X)
    = Complex.I ^ P.phase.val
      * (Complex.I ^ yWeight P.base * (-1) ^ zDot P.base (w + P.base.X) * f (w + P.base.X))
  rw [charOf_pauliErrorPhase_eval hm id P 0 hodd,
    show (fun j => (w + P.base.X) (id j)) = w + P.base.X from rfl, add_zero, pow_add]
  ring

/-- **The move is the run of the Pauli's word**: on a carrier state at the word's precision, at
least `2` where `e + yWeight` is odd, `applyPauli P S` and `run (pauliWord P) S` have the same
amplitude. The run's height grows at each free-rule H, which `StateEq` does not see. Proved at a
later step. -/
theorem applyPauli_stateEq_pauliWord {m : ℕ} (P : PauliGroup n) {S : KernelSumState n}
    (hS : IsCarrier S) (hm : S.m = m) (hodd : (P.phase.val + yWeight P.base) % 2 = 1 → 2 ≤ m) :
    StateEq (applyPauli P S) (run (pauliWord P : GateWord n m) S) := by
  unfold StateEq
  rw [amp_applyPauli, amp_run _ hS hm, runAmp_pauliWord P (hm ▸ hS.1) hodd]

/-! ## Casts of letters -/

/-- A gate word moved along an equality of the number of bits. -/
def castWord {N N' m : ℕ} (h : N = N') (w : GateWord N m) : GateWord N' m := h ▸ w

/-- A Pauli with its sign moved along an equality of the number of bits. -/
def SignedPauli.castBits {N N' : ℕ} (h : N = N') (P : SignedPauli N) : SignedPauli N' := h ▸ P

/-- The cast keeps the number of Y. -/
@[simp] theorem yWeight_castBits {N N' : ℕ} (h : N = N') (P : SignedPauli N) :
    yWeight (P.castBits h).pauli = yWeight P.pauli := by
  subst h
  rfl

/-- A word run on a cast record is the cast of the cast word's run. -/
private theorem run_castWord_castBits {N N' m : ℕ} (h : N = N') (w : GateWord N m)
    (T : KernelSumState N) : run (castWord h w) (castBits h T) = castBits h (run w T) := by
  subst h
  rfl

/-- A word run on a record cast back is the cast back of the cast word's run. -/
private theorem run_castBits_symm {N N' m : ℕ} (h : N = N') (w : GateWord N m)
    (T : KernelSumState N') :
    run w (castBits h.symm T) = castBits h.symm (run (castWord h w) T) := by
  subst h
  rfl

/-- Conditioning a cast record on a cast Pauli is the cast of the conditioning. -/
private theorem conditionOutcome_castBits {N N' : ℕ} (h : N = N') (T : KernelSumState N)
    (P : SignedPauli N) :
    conditionOutcome (castBits h T) (P.castBits h)
      = castBits (congrArg (· + 1) h) (conditionOutcome T P) := by
  subst h
  rfl

/-- Conditioning a record cast back is the cast back of the conditioning on the cast Pauli. -/
private theorem conditionOutcome_castBits_symm {N N' : ℕ} (h : N = N') (T : KernelSumState N')
    (P : SignedPauli N) :
    conditionOutcome (castBits h.symm T) P
      = castBits (congrArg (· + 1) h).symm (conditionOutcome T (P.castBits h)) := by
  subst h
  rfl

/-- Two casts are one cast, along the composite equality. -/
private theorem castBits_castBits_bits {N N' N'' : ℕ} (h : N = N') (h' : N' = N'')
    (T : KernelSumState N) : castBits h' (castBits h T) = castBits (h.trans h') T := by
  subst h
  subst h'
  rfl

namespace Protocol

variable {m : ℕ}

/-! ## Concatenation -/

/-- **Concatenation**: `q`, on the `n + k` free bits `p` ends on, after `p`. Each letter of `q` is
cast along `n + k + j = n + (k + j)`; a suffix after `k` outcome bits is a
`Protocol m (n + k) k'`. -/
def append {k : ℕ} (p : Protocol m n k) : {k' : ℕ} → Protocol m (n + k) k' → Protocol m n (k + k')
  | _, nil => p
  | _, word q w => (p.append q).word (castWord (Nat.add_assoc n k _) w)
  | _, condition q P hP =>
      (p.append q).condition (P.castBits (Nat.add_assoc n k _))
        (by rw [yWeight_castBits]; exact hP)

/-- **The interpretation of a concatenation** is the second protocol's interpretation of the
first's, cast along `n + k + k' = n + (k + k')`. Proved at a later step. -/
theorem interpret_append {k k' : ℕ} (p : Protocol m n k) (q : Protocol m (n + k) k')
    (S : KernelSumState n) :
    (p.append q).interpret S = castBits (Nat.add_assoc n k k') (q.interpret (p.interpret S)) := by
  induction q with
  | nil => rfl
  | word q w ih =>
    change run (castWord (Nat.add_assoc n k _) w) ((p.append q).interpret S) = _
    rw [ih, run_castWord_castBits]
    rfl
  | condition q P hP ih =>
    change conditionOutcome ((p.append q).interpret S) (P.castBits (Nat.add_assoc n k _)) = _
    rw [ih, conditionOutcome_castBits]
    rfl


/-- A protocol moved along an equality of the number of outcome bits. -/
def castOutcomes {k k' : ℕ} (h : k = k') (p : Protocol m n k) : Protocol m n k' := h ▸ p

/-- A protocol cast along an equality of outcome counts interprets to the cast record. -/
private theorem interpret_castOutcomes {k k' : ℕ} (h : k = k') (p : Protocol m n k)
    (S : KernelSumState n) :
    (castOutcomes h p).interpret S = castBits (congrArg (n + ·) h) (p.interpret S) := by
  subst h
  rfl

/-! ## Locations -/

/-- **A location of a protocol**: a gap between two of its letters, the letters of a word counted
one by one. `nil` is the start of the empty protocol; `word ℓ` is the location `ℓ` of `p` in
`p.word w`, before `w`; `letter p w i` the gap after the `i`-th letter of `w`; `condition ℓ` the
location `ℓ` of `p` in `p.condition P hP`; `outcome p P hP` the gap just after the conditioning
letter, where its outcome bit is a free bit. -/
inductive Location : {k : ℕ} → Protocol m n k → Type where
  | nil : Location Protocol.nil
  | word {k : ℕ} {p : Protocol m n k} {w : GateWord (n + k) m} (ℓ : Location p) :
      Location (p.word w)
  | letter {k : ℕ} (p : Protocol m n k) (w : GateWord (n + k) m) (i : Fin w.length) :
      Location (p.word w)
  | condition {k : ℕ} {p : Protocol m n k} {P : SignedPauli (n + k)}
      {hP : yWeight P.pauli % 2 = 1 → 2 ≤ m} (ℓ : Location p) : Location (p.condition P hP)
  | outcome {k : ℕ} (p : Protocol m n k) (P : SignedPauli (n + k))
      (hP : yWeight P.pauli % 2 = 1 → 2 ≤ m) : Location (p.condition P hP)

namespace Location

/-- The number of conditioning letters before the location. -/
def outcomes : {k : ℕ} → {p : Protocol m n k} → Location p → ℕ
  | _, _, nil => 0
  | _, _, word ℓ => ℓ.outcomes
  | _, _, letter (k := k) _ _ _ => k
  | _, _, condition ℓ => ℓ.outcomes
  | _, _, outcome (k := k) _ _ _ => k + 1

/-- The number of conditioning letters after the location. -/
def rest : {k : ℕ} → {p : Protocol m n k} → Location p → ℕ
  | _, _, nil => 0
  | _, _, word ℓ => ℓ.rest
  | _, _, letter _ _ _ => 0
  | _, _, condition ℓ => ℓ.rest + 1
  | _, _, outcome _ _ _ => 0

/-- The conditioning letters before and after a location are all of them. -/
theorem outcomes_add_rest {k : ℕ} {p : Protocol m n k} (ℓ : Location p) :
    ℓ.outcomes + ℓ.rest = k := by
  induction ℓ with
  | nil => rfl
  | word ℓ ih => exact ih
  | letter _ _ _ => rfl
  | condition ℓ ih => simp only [outcomes, rest]; omega
  | outcome _ _ _ => rfl

/-- The register equality a location's split is cast along. -/
theorem bits_eq {k : ℕ} {p : Protocol m n k} (ℓ : Location p) :
    n + k = n + ℓ.outcomes + ℓ.rest := by
  rw [Nat.add_assoc, ℓ.outcomes_add_rest]

/-- **The protocol before the location**: the letters up to the gap. -/
def before : {k : ℕ} → {p : Protocol m n k} → (ℓ : Location p) → Protocol m n ℓ.outcomes
  | _, _, nil => Protocol.nil
  | _, _, word ℓ => ℓ.before
  | _, _, letter p w i => p.word (w.take (i.val + 1))
  | _, _, condition ℓ => ℓ.before
  | _, _, outcome p P hP => p.condition P hP

/-- **The protocol after the location**: the letters from the gap on, on the free bits there,
outcome bits included, its letters cast to them. -/
def after : {k : ℕ} → {p : Protocol m n k} → (ℓ : Location p) →
    Protocol m (n + ℓ.outcomes) ℓ.rest
  | _, _, nil => Protocol.nil
  | _, _, @word _ _ _ _ w ℓ => ℓ.after.word (castWord ℓ.bits_eq w)
  | _, _, letter _ w i => Protocol.nil.word (w.drop (i.val + 1))
  | _, _, @condition _ _ _ _ P hP ℓ =>
      ℓ.after.condition (P.castBits ℓ.bits_eq) (by rw [yWeight_castBits]; exact hP)
  | _, _, outcome _ _ _ => Protocol.nil

end Location

/-- **An error word at a location**: the protocol before it, then the one-word protocol
`nil.word w` on the free bits there, then the protocol after it. -/
def insertAt {k : ℕ} (p : Protocol m n k) (ℓ : Location p) (w : GateWord (n + ℓ.outcomes) m) :
    Protocol m n k :=
  castOutcomes ℓ.outcomes_add_rest ((ℓ.before.append (Protocol.nil.word w)).append ℓ.after)

/-- **A protocol is its split at a location**, up to interpretation: the protocol after the
location run on the interpretation of the protocol before it, cast back to the protocol's free
bits. A split inside a word is `run_append`. -/
private theorem interpret_eq_split {k : ℕ} (p : Protocol m n k) (ℓ : Location p)
    (S : KernelSumState n) :
    p.interpret S = castBits ℓ.bits_eq.symm (ℓ.after.interpret (ℓ.before.interpret S)) := by
  induction ℓ with
  | nil => rfl
  | @word k p w ℓ ih =>
    change run w (p.interpret S) = castBits ℓ.bits_eq.symm
      (run (castWord ℓ.bits_eq w) (ℓ.after.interpret (ℓ.before.interpret S)))
    rw [ih, run_castBits_symm]
  | @letter k p w i =>
    change run w (p.interpret S)
      = castBits (Nat.add_zero (n + k)).symm
          (run (w.drop (i.val + 1)) (run (w.take (i.val + 1)) (p.interpret S)))
    rw [← run_append, List.take_append_drop]
    rfl
  | @condition k p P hP ℓ ih =>
    change conditionOutcome (p.interpret S) P = castBits (congrArg (· + 1) ℓ.bits_eq).symm
      (conditionOutcome (ℓ.after.interpret (ℓ.before.interpret S)) (P.castBits ℓ.bits_eq))
    rw [ih, conditionOutcome_castBits_symm]
  | outcome p P hP => rfl

/-- **A location is a split, and the interpretation with a word inserted there.** First, the
protocol is its split at `ℓ` up to interpretation: the protocol after the location run on the
interpretation of the protocol before it, cast to the protocol's free bits (a split inside a word
by `run_append`). Second, with the word `w` inserted, the protocol after the location runs on
`w`'s run on the interpretation of the protocol before it. Proved at a later step. -/
theorem interpret_insertAt {k : ℕ} (p : Protocol m n k) (ℓ : Location p)
    (w : GateWord (n + ℓ.outcomes) m) (S : KernelSumState n) :
    p.interpret S = castBits ℓ.bits_eq.symm (ℓ.after.interpret (ℓ.before.interpret S))
      ∧ (p.insertAt ℓ w).interpret S
        = castBits ℓ.bits_eq.symm (ℓ.after.interpret (run w (ℓ.before.interpret S))) := by
  refine ⟨interpret_eq_split p ℓ S, ?_⟩
  change (castOutcomes ℓ.outcomes_add_rest
      ((ℓ.before.append (Protocol.nil.word w)).append ℓ.after)).interpret S = _
  rw [interpret_castOutcomes, interpret_append, interpret_append, castBits_castBits_bits]
  rfl

/-- **Words placed at every location**, each in the gap `insertAt` places a word at: the word of
the start first, after each letter of a word and after each conditioning letter the word of the
gap there. -/
def placeWords : {k : ℕ} → (p : Protocol m n k) →
    ((ℓ : Location p) → GateWord (n + ℓ.outcomes) m) → Protocol m n k
  | _, nil, E => Protocol.nil.word (E Location.nil)
  | _, word p w, E =>
      (placeWords p fun ℓ => E (Location.word ℓ)).word
        ((List.finRange w.length).flatMap fun i => w.get i :: E (Location.letter p w i))
  | _, condition p P hP, E =>
      ((placeWords p fun ℓ => E (Location.condition ℓ)).condition P hP).word
        (E (Location.outcome p P hP))

/-- **A fault set**: a Pauli group element on the free bits at every location, the identity where
there is no fault. -/
def FaultSet {k : ℕ} (p : Protocol m n k) : Type :=
  (ℓ : Location p) → PauliGroup (n + ℓ.outcomes)

/-- **The faulty protocol**: the word of each location's Pauli placed there. -/
noncomputable def faulty {k : ℕ} (p : Protocol m n k) (F : FaultSet p) : Protocol m n k :=
  p.placeWords fun ℓ => pauliWord (F ℓ)

/-- **A measurement error**: X on the outcome bit of a conditioning letter, just after it. -/
noncomputable def measurementError {k : ℕ} (p : Protocol m n k) (P : SignedPauli (n + k))
    (hP : yWeight P.pauli % 2 = 1 → 2 ≤ m) : Protocol m n (k + 1) :=
  (p.condition P hP).insertAt (Location.outcome p P hP)
    (pauliWord (⟨0, paulix (Fin.last (n + k))⟩ : PauliGroup (n + (k + 1))))

end Protocol

/-! ## A Pauli chosen by outcome bits -/

/-- **A function of `r` bits as a polynomial**: its indicator expansion
`Σ_s g(s)·Π_i (s_i ? x_i : 1 − x_i)`, the bit `i` read at the variable `ι i`. At every word of bits
it evaluates to `g` of the bits read there. -/
noncomputable def outcomePoly {N r k : ℕ} (ι : Fin r → Fin N) (g : (Fin r → ZMod 2) → ZMod (2 ^ k)) :
    DiagPhase N k :=
  ∑ s : Fin r → ZMod 2, MvPolynomial.C (g s)
    * ∏ i : Fin r, if s i = 1 then MvPolynomial.X (ι i) else 1 - MvPolynomial.X (ι i)

/-- **The Pauli `d(s)` applied at outcome string `s`**, on `n` data bits and `r` outcome bits at
precision `m`: one diagonal letter `2^{m−1}·Σ_j d^Z_j(s)·w_j + 2^{m−2}·(e(s) + yWeight(d(s).base))`,
then for each data bit `j`, H on `j`, the diagonal letter `2^{m−1}·d^X_j(s)·w_j`, H on `j`. Each
function of `s` is its `outcomePoly`; the outcome bits are read and never changed. -/
noncomputable def outcomePauliWord {r m : ℕ} (d : (Fin r → ZMod 2) → PauliGroup n) :
    GateWord (n + r) m :=
  GateLetter.diagonal
      (MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1))
          * ∑ j : Fin n, outcomePoly (Fin.natAdd n) (fun s => (((d s).base.Z j).val : ZMod (2 ^ m)))
              * MvPolynomial.X (Fin.castAdd r j)
        + outcomePoly (Fin.natAdd n)
            (fun s => iPowExp m ((d s).phase.val + yWeight (d s).base)))
    :: (List.finRange n).flatMap fun j =>
      [GateLetter.hadamard (Fin.castAdd r j),
        GateLetter.diagonal
          (MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1))
            * outcomePoly (Fin.natAdd n) (fun s => (((d s).base.X j).val : ZMod (2 ^ m)))
            * MvPolynomial.X (Fin.castAdd r j)),
        GateLetter.hadamard (Fin.castAdd r j)]

/-- An outcome bit is not a data bit. -/
private theorem natAdd_ne_castAdd_bits {r : ℕ} (i : Fin r) (j : Fin n) :
    Fin.natAdd n i ≠ Fin.castAdd r j := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_natAdd, Fin.val_castAdd] at hv
  have hj := j.isLt
  omega

/-- **The indicator expansion evaluates to the function**: at every word, `outcomePoly ι g` is `g`
of the bits read through `ι`. -/
private theorem eval_outcomePoly_bits {N r k : ℕ} (ι : Fin r → Fin N)
    (g : (Fin r → ZMod 2) → ZMod (2 ^ k)) (v : Fin N → ZMod 2) :
    (outcomePoly ι g).eval v = g (fun i => v (ι i)) := by
  unfold outcomePoly
  simp only [DiagPhase.eval, map_sum, map_mul, map_prod, MvPolynomial.eval_C]
  rw [Finset.sum_eq_single (fun i => v (ι i))]
  · rw [Finset.prod_eq_one, mul_one]
    intro i _
    beta_reduce
    rcases bit_cases_pauliWord (v (ι i)) with h | h
    · rw [if_neg (by rw [h]; decide)]
      simp [DiagPhase.liftBinary, h]
    · rw [if_pos h]
      simp [DiagPhase.liftBinary, h]
  · intro s _ hs
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hs
    rw [Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
    rcases bit_cases_pauliWord (s i) with h | h <;>
      rcases bit_cases_pauliWord (v (ι i)) with h' | h'
    · exact absurd (h.trans h'.symm) hi
    · rw [if_neg (by rw [h]; decide)]
      simp [DiagPhase.liftBinary, h']
    · rw [if_pos h]
      simp [DiagPhase.liftBinary, h']
    · exact absurd (h.trans h'.symm) hi
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The words on the data and outcome bits that are zero on the outcome bits. -/
private def outcomeDataBits (n r : ℕ) : Submodule (ZMod 2) (Fin (n + r) → ZMod 2) :=
  LinearMap.ker (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.natAdd n : Fin r → Fin (n + r)))

/-- A word is in `outcomeDataBits` when it is zero on every outcome bit. -/
private theorem mem_outcomeDataBits {r : ℕ} {u : Fin (n + r) → ZMod 2} :
    u ∈ outcomeDataBits n r ↔ ∀ i : Fin r, u (Fin.natAdd n i) = 0 := by
  unfold outcomeDataBits
  rw [LinearMap.mem_ker]
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

/-- The translation that `outcomePauliWord`'s letters on data bit `j` make at the word `v`:
`d^X_j(s)·e_j`, where `s` is the outcome bits of `v`. -/
private noncomputable def outcomeShift {r : ℕ} (d : (Fin r → ZMod 2) → PauliGroup n) (j : Fin n)
    (v : Fin (n + r) → ZMod 2) : Fin (n + r) → ZMod 2 :=
  (d (fun i => v (Fin.natAdd n i))).base.X j
    • (Pi.single (Fin.castAdd r j) 1 : Fin (n + r) → ZMod 2)

/-- The translation is zero on the outcome bits. -/
private theorem outcomeShift_mem {r : ℕ} (d : (Fin r → ZMod 2) → PauliGroup n) (j : Fin n)
    (v : Fin (n + r) → ZMod 2) : outcomeShift d j v ∈ outcomeDataBits n r := by
  rw [mem_outcomeDataBits]
  intro i
  rw [outcomeShift, Pi.smul_apply, Pi.single_eq_of_ne (natAdd_ne_castAdd_bits i j), smul_zero]

/-- The translation reads only the outcome bits, which a translation by `outcomeDataBits` keeps. -/
private theorem outcomeShift_add {r : ℕ} (d : (Fin r → ZMod 2) → PauliGroup n) (j : Fin n)
    (v u : Fin (n + r) → ZMod 2) (hu : u ∈ outcomeDataBits n r) :
    outcomeShift d j (v + u) = outcomeShift d j v := by
  have hread : (fun i => (v + u) (Fin.natAdd n i)) = fun i => v (Fin.natAdd n i) := by
    funext i
    rw [Pi.add_apply, mem_outcomeDataBits.mp hu i, add_zero]
  rw [outcomeShift, outcomeShift, hread]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 equation:he6e827075ed8
/-- One data bit's letters of `outcomePauliWord`: H, the half turn on the bit controlled by
`d^X_j(s)`, H translate by `d^X_j(s)·e_j`. -/
private theorem runAmp_outcomePauliWord_bit {r m : ℕ} (d : (Fin r → ZMod 2) → PauliGroup n)
    (hm : 1 ≤ m) (j : Fin n) (g : (Fin (n + r) → ZMod 2) → ℂ) :
    runAmp ([GateLetter.hadamard (Fin.castAdd r j),
        GateLetter.diagonal
          (MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1))
            * outcomePoly (Fin.natAdd n) (fun s => (((d s).base.X j).val : ZMod (2 ^ m)))
            * MvPolynomial.X (Fin.castAdd r j)),
        GateLetter.hadamard (Fin.castAdd r j)] : GateWord (n + r) m) g
      = fun v => g (v + outcomeShift d j v) := by
  refine runAmp_hadamardSandwich (Fin.castAdd r j) _
    (fun v => (d (fun i => v (Fin.natAdd n i))).base.X j) ?_ ?_ g
  · intro v
    rw [DiagPhase.eval_mul, DiagPhase.eval_mul, DiagPhase.eval_C, eval_outcomePoly_bits,
      DiagPhase.eval_X, mul_assoc, ← Nat.cast_mul, charOf_two_pow_mul hm]
  · intro v b
    have hread : (fun i => Function.update v (Fin.castAdd r j) b (Fin.natAdd n i))
        = fun i => v (Fin.natAdd n i) :=
      funext fun i => Function.update_of_ne (natAdd_ne_castAdd_bits i j) b v
    change (d (fun i => Function.update v (Fin.castAdd r j) b (Fin.natAdd n i))).base.X j
      = (d (fun i => v (Fin.natAdd n i))).base.X j
    rw [hread]

/-- At `w ++ s`, the translations of all the data bits add up to `(w + d^X(s)) ++ s`. -/
private theorem append_add_outcomeShift {r : ℕ} (d : (Fin r → ZMod 2) → PauliGroup n)
    (w : Fin n → ZMod 2) (s : Fin r → ZMod 2) :
    Fin.append w s + ((List.finRange n).map fun j => outcomeShift d j (Fin.append w s)).sum
      = Fin.append (w + (d s).base.X) s := by
  have hs : (fun i => Fin.append w s (Fin.natAdd n i)) = s :=
    funext fun i => Fin.append_right w s i
  rw [← Fin.sum_univ_def]
  funext l
  rw [Pi.add_apply, Finset.sum_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [Fin.append_left, Fin.append_left, Pi.add_apply, Finset.sum_eq_single i]
    · rw [outcomeShift, hs, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro j _ hji
      have hne : Fin.castAdd r i ≠ Fin.castAdd r j :=
        fun h => hji (Fin.castAdd_injective n r h).symm
      rw [outcomeShift, Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Fin.append_right, Fin.append_right, Finset.sum_eq_zero, add_zero]
    intro j _
    exact mem_outcomeDataBits.mp (outcomeShift_mem d j _) i

/-- A sum's value is the sum of the values. -/
private theorem eval_sum_bits {N m : ℕ} {α : Type*} (s : Finset α) (F : α → DiagPhase N m)
    (v : Fin N → ZMod 2) : (∑ a ∈ s, F a).eval v = ∑ a ∈ s, (F a).eval v :=
  map_sum (MvPolynomial.eval (DiagPhase.liftBinary v)) F s

/-- **The phase letter of `outcomePauliWord`** at `u ++ s`: the sign `(−1)^{z(s)·u}` of the Z-part
of `d(s)`, times `i^{e(s) + yWeight(d(s).base)}`. -/
private theorem charOf_outcomePhase_eval {r m : ℕ} (d : (Fin r → ZMod 2) → PauliGroup n)
    (hm : 1 ≤ m) (s : Fin r → ZMod 2)
    (hodd : ((d s).phase.val + yWeight (d s).base) % 2 = 1 → 2 ≤ m) (u : Fin n → ZMod 2) :
    charOf m (DiagPhase.eval
      (MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1))
          * ∑ j : Fin n, outcomePoly (Fin.natAdd n)
              (fun s => (((d s).base.Z j).val : ZMod (2 ^ m)))
              * MvPolynomial.X (Fin.castAdd r j)
        + outcomePoly (Fin.natAdd n)
            (fun s => iPowExp m ((d s).phase.val + yWeight (d s).base))) (Fin.append u s))
      = (-1) ^ zDot (d s).base u * Complex.I ^ ((d s).phase.val + yWeight (d s).base) := by
  have hs : (fun i => Fin.append u s (Fin.natAdd n i)) = s :=
    funext fun i => Fin.append_right u s i
  have hsum : DiagPhase.eval (∑ j : Fin n, outcomePoly (Fin.natAdd n)
        (fun s => (((d s).base.Z j).val : ZMod (2 ^ m))) * MvPolynomial.X (Fin.castAdd r j))
        (Fin.append u s)
      = ((zDot (d s).base u : ℕ) : ZMod (2 ^ m)) := by
    rw [eval_sum_bits]
    unfold zDot
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [DiagPhase.eval_mul, eval_outcomePoly_bits, DiagPhase.eval_X, hs, Fin.append_left,
      Nat.cast_mul]
  rw [DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, hsum, eval_outcomePoly_bits, hs,
    charOf_add, charOf_two_pow_mul hm, charOf_iPowExp _ hm hodd]

/-- **The referee of the outcome-controlled Pauli**: at every outcome string `s`, the run on `f` is
`d(s).act` on the slice `f(·, s)`. It needs a positive precision, and at least `2` where
`e(s) + yWeight(d(s).base)` is odd, as T13's `hodd`: the condition is asked only at `s`, the
weakest form, and holds at every `s` where the target's text asks it of some `s`. Proved at a
later step. -/
theorem runAmp_outcomePauliWord {r m : ℕ} (d : (Fin r → ZMod 2) → PauliGroup n) (hm : 1 ≤ m)
    (f : (Fin (n + r) → ZMod 2) → ℂ) (s : Fin r → ZMod 2)
    (hodd : ((d s).phase.val + yWeight (d s).base) % 2 = 1 → 2 ≤ m) :
    (fun w => runAmp (outcomePauliWord d : GateWord (n + r) m) f (Fin.append w s))
      = (d s).act (fun w => f (Fin.append w s)) := by
  unfold outcomePauliWord
  rw [runAmp_cons, runAmp_flatMap_translate (outcomeDataBits n r) _ (outcomeShift d)
    (List.finRange n) (fun j _ v => outcomeShift_mem d j v)
    (fun j _ v u hu => outcomeShift_add d j v u hu)
    (fun j _ g => runAmp_outcomePauliWord_bit d hm j g)]
  funext w
  beta_reduce
  rw [append_add_outcomeShift]
  change charOf m (DiagPhase.eval _ (Fin.append (w + (d s).base.X) s))
      * f (Fin.append (w + (d s).base.X) s)
    = Complex.I ^ (d s).phase.val * (Complex.I ^ yWeight (d s).base
      * (-1) ^ zDot (d s).base (w + (d s).base.X) * f (Fin.append (w + (d s).base.X) s))
  rw [charOf_outcomePhase_eval d hm s hodd, pow_add]
  ring

end FTQCLib.Frame.Walkthrough

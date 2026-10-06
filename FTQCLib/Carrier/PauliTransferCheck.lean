/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.PauliTransfer
import FTQCLib.Gates.Hadamard

/-!
# Check: T50, the Walsh transform and the Pauli transfer matrix

T50.2's witness rows (`docs/STEPS.md`) on the frozen statement of `PauliTransfer.lean`. Every row
is about one data bit, in the order `(I, X, Z, XZ)` and the convention `P = X^a Z^b` with `P†` in
the transfer matrix, and about the objects the headlines name: the transfer matrix of a
protocol's branch (`ptm (channelBranch p σ o)`), its χ (`chi p σ o`), the Bell reading
(`bellRead p σ`) and the Pauli coefficients of the Kraus operator (`pauliCoeff (krausOp p σ o e)`).
Every T50 headline (`walsh2n_eq_runAmp`, `bellRead_choi_eq_pauliCoeff`, `channel_eq_chi_sum`,
`ptm_eq_chi_basis`, `ptm_diag_eq_walsh_chi_diag`, `pauliChannel_iff_chi_diagonal`,
`chi_diag_isDistribution`) was `sorry`'d when the rows below were written at T50.2 and is proved
now, at T50.3.1 and T50.3.2; none of the rows uses one, each being computed instead through the
same routes the witness took, straight from the definitions (below), which stayed available once
the headlines were proved. The routes:

* **The transfer matrix**, from its definition: the branch is `channelBranch`, T49's `channel`
  at the read string, whose entries are the dilation's (`ptm_branch_apply`), and each entry of the
  dilation is the referee on a point mass (`dilation_none`, `dilation_unread`), evaluated letter by
  letter at each input (`kraus_hadamard`, `kraus_X`, ...).
* **χ**, from its definition: `2^{−1}` times the Gram data of the Bell reading over the unread
  bits. The Bell reading's amplitude is T05's referee of `bellReadWord` (`amp_run`) on T49's
  read Choi state, whose amplitude is the referee on a point mass (T49's `amp_choi`), so at
  `(b, a, o, e)` it is `(1/√2)(K(a | 0) + (−1)^b K(a + 1 | 1))` with `K` the dilation's block at
  `(o, e)` (`bellRead_none`, `bellRead_unread`): the CNOT and the H written out, not
  `bellRead_choi_eq_pauliCoeff`.

The rows:

* **H (agreement).** The transfer matrix of H is the symplectic swap of X and Z: `R(P, Q)` is
  `(−1)^{a·b}` at `P = hadamardAt 0 Q` (`FTQCLib/Gates/Hadamard.lean`) and `0` elsewhere, the sign
  at `XZ` being the real convention's `H XZ H = −XZ`; the source's table of H on Pauli strings.
* **The bit flip at `p = ½` (agreement).** Conditioning on X with the outcome unread is
  `ρ ↦ ½ρ + ½XρX`: χ's diagonal is `(½, ½, 0, 0)` and the transfer matrix's `(1, 1, 0, 0)`.
* **The unitary X (discriminating).** X as the word `H Z H`: χ's diagonal is `δ_X`, a distribution,
  and the transfer matrix's diagonal is `(1, 1, −1, −1)`, not one. The distribution is χ's
  diagonal, never the transfer matrix's (the correction of 2026-10-02).
* **The identity at `n = 1` (discriminating).** The Bell reading of the empty protocol is `√2` at
  `I`, where `c(I) = 1`: the factor `2^{n/2}` of T49's unnormalised floor.
* **Z-conditioning with the outcome unread (agreement).** A Pauli channel whose distribution is
  χ's diagonal `(½, 0, ½, 0)`, with χ zero off the diagonal.
* **The T gate (discriminating).** χ is not diagonal (`χ(I, Z) ≠ 0`), and the transfer matrix's
  diagonal is still `2 Ŵ` of χ's diagonal at every `Q`: the duality needs no Pauli-channel
  hypothesis.

Scope (standard 7.3): every row is about one data bit, at precisions `1` and `3`, and proves
nothing about other registers.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Matrix

/-! ## The four Paulis on one bit, and finite sums -/

/-- `I` on one bit. -/
def transferPauliI : Pauli 1 := ⟨![0], ![0]⟩

/-- `X` on one bit. -/
def transferPauliX : Pauli 1 := ⟨![1], ![0]⟩

/-- `Z` on one bit. -/
def transferPauliZ : Pauli 1 := ⟨![0], ![1]⟩

/-- `XZ` on one bit. -/
def transferPauliXZ : Pauli 1 := ⟨![1], ![1]⟩

/-- A sum over the words of one bit. -/
private theorem sum_bits_one {M : Type*} [AddCommMonoid M] (f : (Fin 1 → ZMod 2) → M) :
    ∑ x, f x = f ![0] + f ![1] := by
  rw [← (Equiv.funUnique (Fin 1) (ZMod 2)).symm.sum_comp, sum_zmod_two]
  congr 2 <;> funext i <;> fin_cases i <;> rfl

/-- A sum over the one word of no bits. -/
private theorem sum_bits_zero {M : Type*} [AddCommMonoid M] (f : (Fin 0 → ZMod 2) → M) :
    ∑ x, f x = f 0 := by
  rw [Fintype.sum_unique]
  exact congrArg f (Subsingleton.elim _ _)

/-- A sum over the four Paulis on one bit, in the order `(I, X, Z, XZ)`. -/
private theorem sum_pauli_one {M : Type*} [AddCommMonoid M] (f : Pauli 1 → M) :
    ∑ P, f P = f transferPauliI + f transferPauliX + f transferPauliZ + f transferPauliXZ := by
  have e : ∑ P, f P = ∑ xz : (Fin 1 → ZMod 2) × (Fin 1 → ZMod 2), f ⟨xz.1, xz.2⟩ :=
    Fintype.sum_equiv (Pauli.linearEquivProd (n := 1)).toEquiv _ _ (fun _ => rfl)
  rw [e, Fintype.sum_prod_type, sum_bits_one, sum_bits_one, sum_bits_one]
  simp only [transferPauliI, transferPauliX, transferPauliZ, transferPauliXZ]
  abel

/-- Every Pauli on one bit is one of the four. -/
private theorem pauli_one_cases (P : Pauli 1) :
    P = transferPauliI ∨ P = transferPauliX ∨ P = transferPauliZ ∨ P = transferPauliXZ := by
  obtain ⟨a, b⟩ := P
  have ha : a = ![a 0] := by funext i; fin_cases i; rfl
  have hb : b = ![b 0] := by funext i; fin_cases i; rfl
  rw [ha, hb]
  rcases zmod_two_dichotomy (a 0) with h | h <;> rcases zmod_two_dichotomy (b 0) with h' | h' <;>
    simp [h, h', transferPauliI, transferPauliX, transferPauliZ, transferPauliXZ]

/-- A word of one bit is its one value. -/
private theorem bits_one (x : Fin 1 → ZMod 2) : x = ![x 0] := by
  funext i
  fin_cases i
  rfl

/-- `pauliMatrix` on one bit: `X^a Z^b` sends `∣y⟩` to `(−1)^{b·y} ∣y + a⟩`. -/
private theorem pauliMatrix_apply (a b x y : ZMod 2) :
    pauliMatrix ⟨![a], ![b]⟩ ![x] ![y] = if x = y + a then signOf (b * y) else 0 := by
  rcases zmod_two_dichotomy a with rfl | rfl <;> rcases zmod_two_dichotomy b with rfl | rfl <;>
    rcases zmod_two_dichotomy x with rfl | rfl <;> rcases zmod_two_dichotomy y with rfl | rfl <;>
    simp (config := {decide := true}) [pauliMatrix, zDot, signOf_zero, signOf_one]

/-- H on one bit is the swap of the X and Z bits. -/
private theorem hadamardAt_one (Q : Pauli 1) : FTQCLib.Gates.hadamardAt 0 Q = ⟨Q.Z, Q.X⟩ := by
  ext i <;> fin_cases i <;> rfl

/-! ## `1/√2` and the T phase -/

/-- `1/√2`, H's scale. -/
private noncomputable def invSqrtTwo : ℂ := (Real.sqrt 2 : ℂ)⁻¹

private theorem invSqrtTwo_sq : invSqrtTwo ^ 2 = 2⁻¹ := by
  rw [invSqrtTwo, inv_pow, sqrt_two_sq_complex]

private theorem invSqrtTwo_pow_three : invSqrtTwo ^ 3 = 2⁻¹ * invSqrtTwo := by
  rw [pow_succ, invSqrtTwo_sq]

private theorem invSqrtTwo_pow_four : invSqrtTwo ^ 4 = 4⁻¹ := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, invSqrtTwo_sq]
  norm_num

private theorem conj_invSqrtTwo : starRingEnd ℂ invSqrtTwo = invSqrtTwo := by
  rw [invSqrtTwo, map_inv₀, Complex.conj_ofReal]

private theorem invSqrtTwo_ne_zero : invSqrtTwo ≠ 0 := by
  refine inv_ne_zero ?_
  rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
  norm_num

/-- The T phase `ζ₈ = (1 + i)/√2` (`charOf_three_one`). -/
private theorem charOf_three_one_eq : charOf 3 1 = (1 + Complex.I) * invSqrtTwo := by
  rw [charOf_three_one, invSqrtTwo, div_eq_mul_inv]

/-! ## The protocols and the readings -/

/-- No outcome bits. -/
def transferNone : Fin 0 ≃ Fin (0 + 0) := Equiv.refl _

/-- The one outcome bit unread. -/
def transferUnread : Fin 1 ≃ Fin (0 + 1) := Equiv.refl _

/-- The empty protocol on one data bit: the identity channel. -/
noncomputable def transferIdentity : Protocol 1 1 0 := Protocol.nil

/-- H on the one data bit. -/
noncomputable def transferHadamard : Protocol 1 1 0 := Protocol.nil.word [GateLetter.hadamard 0]

/-- The unitary X on the one data bit, as the word `H Z H` at precision `1`. -/
noncomputable def transferUnitaryX : Protocol 1 1 0 :=
  Protocol.nil.word [GateLetter.hadamard 0, GateLetter.diagonal (MvPolynomial.X 0),
    GateLetter.hadamard 0]

/-- The T gate on the one data bit: the phase `charOf 3 x`, at precision `3`. -/
noncomputable def transferT : Protocol 3 1 0 :=
  Protocol.nil.word [GateLetter.diagonal (MvPolynomial.X 0)]

/-- Conditioning on X of the one data bit; with the outcome unread, the bit flip at `p = ½`. -/
noncomputable def transferBitFlip : Protocol 1 1 1 :=
  Protocol.nil.condition ⟨0, transferPauliX⟩ (fun h => absurd h (by decide))

/-- Conditioning on Z of the one data bit. -/
noncomputable def transferZCondition : Protocol 1 1 1 :=
  Protocol.nil.condition ⟨0, zPauli (Pi.single 0 1)⟩ (zPauli_precision 1 _)

/-! ## The referees on point masses, letter by letter -/

/-- Split a bit into its two values, as literals. -/
local macro "bit_cases " a:ident : tactic =>
  `(tactic| (rcases zmod_two_dichotomy $a with h | h <;> subst h))

private theorem kraus_identity (a b : ZMod 2) :
    transferIdentity.interpretAmp (delta ![a]) ![b] = if b = a then 1 else 0 := by
  bit_cases a <;> bit_cases b <;> simp (config := {decide := true}) [transferIdentity, delta]

private theorem kraus_hadamard (a b : ZMod 2) :
    transferHadamard.interpretAmp (delta ![a]) ![b] = signOf (a * b) * invSqrtTwo := by
  bit_cases a <;> bit_cases b <;>
    simp (config := {decide := true}) [transferHadamard, runAmp_cons, runAmp_nil, letterAmp,
      walshTransform, delta, signOf_zero, signOf_one, invSqrtTwo]

/-- H twice on a point mass: `(1/√2)(1/√2 + 1/√2) = 1`. -/
private theorem inv_sqrt_two_mul_two :
    (Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ)⁻¹ + (Real.sqrt 2 : ℂ)⁻¹) = 1 := by
  have h := invSqrtTwo_sq
  rw [invSqrtTwo] at h
  linear_combination 2 * h

private theorem kraus_X (a b : ZMod 2) :
    transferUnitaryX.interpretAmp (delta ![a]) ![b] = if b = a + 1 then 1 else 0 := by
  bit_cases a <;> bit_cases b <;>
    simp (config := {decide := true}) [transferUnitaryX, runAmp_cons, runAmp_nil, letterAmp,
      walshTransform, delta, signOf_zero, signOf_one, DiagPhase.eval, MvPolynomial.eval_X,
      DiagPhase.liftBinary, charOf_zero, charOf_one_one, inv_sqrt_two_mul_two]

private theorem kraus_T (a b : ZMod 2) :
    transferT.interpretAmp (delta ![a]) ![b]
      = (if b = a then 1 else 0) * (if a = 0 then 1 else (1 + Complex.I) * invSqrtTwo) := by
  rw [← charOf_three_one_eq]
  bit_cases a <;> bit_cases b <;>
    simp (config := {decide := true}) [transferT, runAmp_cons, runAmp_nil, letterAmp, delta,
      DiagPhase.eval, MvPolynomial.eval_X, DiagPhase.liftBinary, charOf_zero]
  congr 1

private theorem kraus_bitFlip (a b c : ZMod 2) :
    transferBitFlip.interpretAmp (delta ![a]) ![b, c]
      = 2⁻¹ * ((if b = a then 1 else 0) + signOf c * (if b = a + 1 then 1 else 0)) := by
  bit_cases a <;> bit_cases b <;> bit_cases c <;>
    simp (config := {decide := true}) [transferBitFlip, transferPauliX, delta,
      pauliProjection_apply, shiftFactor, zDot, yWeight, Fin.init, signOf_zero, signOf_one]

private theorem kraus_zCondition (a b c : ZMod 2) :
    transferZCondition.interpretAmp (delta ![a]) ![b, c] = if b = a ∧ c = a then 1 else 0 := by
  bit_cases a <;> bit_cases b <;> bit_cases c <;>
    simp (config := {decide := true}) [transferZCondition, delta, pauliProjection_apply,
      shiftFactor, zDot, yWeight, zPauli, Fin.init]
  all_goals norm_num

/-! ## The dilation's entries -/

/-- With no outcome bits, the dilation's entry is the referee on a point mass. -/
private theorem dilation_none {m : ℕ} (p : Protocol m 1 0) (w x : Fin 1 → ZMod 2)
    (o e : Fin 0 → ZMod 2) :
    dilation p transferNone ((w, o), e) x = p.interpretAmp (delta ![x 0]) ![w 0] := by
  unfold dilation
  rw [← bits_one x]
  congr 1
  funext i
  fin_cases i
  rfl

/-- With the one outcome bit unread, the dilation's entry is the referee on a point mass, read
at the data bit and the outcome bit. -/
private theorem dilation_unread {m : ℕ} (p : Protocol m 1 1) (w x : Fin 1 → ZMod 2)
    (o : Fin 0 → ZMod 2) (e : Fin 1 → ZMod 2) :
    dilation p transferUnread ((w, o), e) x = p.interpretAmp (delta ![x 0]) ![w 0, e 0] := by
  unfold dilation
  rw [← bits_one x]
  congr 1
  funext i
  fin_cases i <;> rfl

/-! ## The transfer matrix from its definition -/

/-- The transfer matrix of a branch on one data bit, written out from `ptm`, `channelBranch` and
T49's `channel`: `R(P, Q) = ½ Σ_{i,j} conj P(j, i) Σ_e Σ_{x,x'} K_e(j, x) Q(x, x') conj K_e(i, x')`,
with `K_e` the dilation's block at the read string `o` and the unread string `e`. -/
private theorem ptm_branch_apply {m k r u : ℕ} (p : Protocol m 1 k) (σ : Fin k ≃ Fin (r + u))
    (o : Fin r → ZMod 2) (P Q : Pauli 1) :
    ptm (channelBranch p σ o) P Q = (2 : ℂ)⁻¹ * ∑ i, ∑ j, starRingEnd ℂ (pauliMatrix P j i) *
      ∑ e : Fin u → ZMod 2, ∑ x', ∑ x, dilation p σ ((j, o), e) x * pauliMatrix Q x x'
        * starRingEnd ℂ (dilation p σ ((i, o), e) x') := by
  unfold ptm channelBranch channel
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, pow_one, Finset.sum_mul]

/-! ## The Bell reading from its definition -/

/-- The read Choi state is a carrier state at the protocol's precision (T49's `isCarrier_choi`,
kept by the reindexing). -/
private theorem isCarrier_choiRead {m k r u : ℕ} (p : Protocol m 1 k) (σ : Fin k ≃ Fin (r + u))
    (hm : 1 ≤ m) : IsCarrier (choiRead p σ) ∧ (choiRead p σ).m = m := by
  refine ⟨isCarrier_reindexFreeBits _ _ (isCarrier_choi p hm).1, ?_⟩
  have hcast : ∀ {N N' : ℕ} (h : N = N') (S : KernelSumState N), (castBits h S).m = S.m := by
    intro _ _ h S
    subst h
    rfl
  unfold choiRead reindexFreeBits
  rw [hcast]
  exact (isCarrier_choi p hm).2

/-- The Bell reading on one data bit, by T05's `amp_run`: CNOT from the reference bit to the data
bit, then H on the reference bit. -/
private theorem amp_bellRead_route {m k r u : ℕ} (p : Protocol m 1 k) (σ : Fin k ≃ Fin (r + u))
    (hm : 1 ≤ m) (W : Fin (((1 + 1) + r) + u) → ZMod 2) :
    amp (bellRead p σ) W = invSqrtTwo * (amp (choiRead p σ)
        (DiagPhase.cnotBitMap (doubledBit 1 r u 0) (doubledBit 1 r u 1)
          (Function.update W (doubledBit 1 r u 0) 0))
      + signOf (W (doubledBit 1 r u 0)) * amp (choiRead p σ)
        (DiagPhase.cnotBitMap (doubledBit 1 r u 0) (doubledBit 1 r u 1)
          (Function.update W (doubledBit 1 r u 0) 1))) := by
  unfold bellRead
  rw [amp_run _ (isCarrier_choiRead p σ hm).1 (isCarrier_choiRead p σ hm).2]
  simp only [bellReadWord, List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append,
    runAmp_cons, runAmp_nil, letterAmp, walshTransform, invSqrtTwo, one_div]
  rfl

/-- The Bell reading with no outcome bits, at `(b, a)`: `(1/√2)(K(a | 0) + (−1)^b K(a + 1 | 1))`,
from T49's `amp_choi`. -/
private theorem bellRead_none {m : ℕ} (p : Protocol m 1 0) (hm : 1 ≤ m) (P : Pauli 1)
    (o e : Fin 0 → ZMod 2) :
    amp (bellRead p transferNone) (Fin.append (Fin.append (symplecticBits P) o) e)
      = invSqrtTwo * (dilation p transferNone ((![P.X 0], o), e) ![0]
        + signOf (P.Z 0) * dilation p transferNone ((![P.X 0 + 1], o), e) ![1]) := by
  rw [amp_bellRead_route p transferNone hm]
  unfold choiRead
  rw [amp_reindexFreeBits]
  have hV : ∀ t : ZMod 2, DiagPhase.cnotBitMap (doubledBit 1 0 0 0) (doubledBit 1 0 0 1)
      (Function.update (Fin.append (Fin.append (symplecticBits P) o) e) (doubledBit 1 0 0 0) t)
        ∘ readingEquiv (1 + 1) transferNone
      = Fin.append ![t] ![P.X 0 + t] ∘ Fin.cast (Nat.add_assoc 1 1 0) := by
    intro t
    funext i
    fin_cases i <;> rfl
  have hW : (Fin.append (Fin.append (symplecticBits P) o) e) (doubledBit 1 0 0 0) = P.Z 0 := rfl
  beta_reduce
  rw [hV, hV, amp_choi p hm, amp_choi p hm, hW, dilation_none, dilation_none]
  simp

/-- The Bell reading with the one outcome bit unread, at `(b, a, e)`:
`(1/√2)(K_e(a | 0) + (−1)^b K_e(a + 1 | 1))`, from T49's `amp_choi`. -/
private theorem bellRead_unread {m : ℕ} (p : Protocol m 1 1) (hm : 1 ≤ m) (P : Pauli 1)
    (o : Fin 0 → ZMod 2) (e : Fin 1 → ZMod 2) :
    amp (bellRead p transferUnread) (Fin.append (Fin.append (symplecticBits P) o) e)
      = invSqrtTwo * (dilation p transferUnread ((![P.X 0], o), e) ![0]
        + signOf (P.Z 0) * dilation p transferUnread ((![P.X 0 + 1], o), e) ![1]) := by
  rw [amp_bellRead_route p transferUnread hm]
  unfold choiRead
  rw [amp_reindexFreeBits]
  have hV : ∀ t : ZMod 2, DiagPhase.cnotBitMap (doubledBit 1 0 1 0) (doubledBit 1 0 1 1)
      (Function.update (Fin.append (Fin.append (symplecticBits P) o) e) (doubledBit 1 0 1 0) t)
        ∘ readingEquiv (1 + 1) transferUnread
      = Fin.append ![t] ![P.X 0 + t, e 0] ∘ Fin.cast (Nat.add_assoc 1 1 1) := by
    intro t
    funext i
    fin_cases i <;> rfl
  have hW : (Fin.append (Fin.append (symplecticBits P) o) e) (doubledBit 1 0 1 0) = P.Z 0 := rfl
  beta_reduce
  rw [hV, hV, amp_choi p hm, amp_choi p hm, hW, dilation_unread, dilation_unread]
  simp

/-! ## χ from its definition -/

/-- χ with no outcome bits: `½` times the Bell reading at `P` times its conjugate at `Q`. -/
private theorem chi_none_apply {m : ℕ} (p : Protocol m 1 0) (hm : 1 ≤ m) (P Q : Pauli 1) :
    chi p transferNone 0 P Q = 2⁻¹ * (invSqrtTwo * (dilation p transferNone ((![P.X 0], 0), 0) ![0]
        + signOf (P.Z 0) * dilation p transferNone ((![P.X 0 + 1], 0), 0) ![1])
      * starRingEnd ℂ (invSqrtTwo * (dilation p transferNone ((![Q.X 0], 0), 0) ![0]
        + signOf (Q.Z 0) * dilation p transferNone ((![Q.X 0 + 1], 0), 0) ![1]))) := by
  unfold chi gram
  simp only [bellRead_none p hm, sum_bits_zero, pow_one]

/-- χ with the one outcome bit unread: `½` times the Bell reading's Gram data over that bit. -/
private theorem chi_unread_apply {m : ℕ} (p : Protocol m 1 1) (hm : 1 ≤ m) (P Q : Pauli 1) :
    chi p transferUnread 0 P Q = 2⁻¹ * ∑ e : Fin 1 → ZMod 2,
      invSqrtTwo * (dilation p transferUnread ((![P.X 0], 0), e) ![0]
        + signOf (P.Z 0) * dilation p transferUnread ((![P.X 0 + 1], 0), e) ![1])
      * starRingEnd ℂ (invSqrtTwo * (dilation p transferUnread ((![Q.X 0], 0), e) ![0]
        + signOf (Q.Z 0) * dilation p transferUnread ((![Q.X 0 + 1], 0), e) ![1])) := by
  unfold chi gram
  simp only [bellRead_unread p hm]
  norm_num

/-- Evaluate an entry of χ or of the transfer matrix of a concrete protocol on one data bit:
the sums over one bit, the dilation's entries, the Paulis' matrices, then arithmetic with
`(1/√2)² = ½` and `i² = −1`. -/
local macro "entry_eval" : tactic =>
  `(tactic| (
    simp only [sum_bits_one, sum_bits_zero, dilation_none, dilation_unread, transferPauliI,
      transferPauliX, transferPauliZ, transferPauliXZ, pauliMatrix_apply, Matrix.cons_val_zero]
    simp (config := {decide := true}) [kraus_identity, kraus_hadamard, kraus_X, kraus_T,
      kraus_bitFlip, kraus_zCondition, signOf_zero, signOf_one, conj_invSqrtTwo, map_ofNat,
      map_inv₀, Complex.conj_I]
    all_goals (try ring_nf)
    all_goals (try simp only [invSqrtTwo_sq, invSqrtTwo_pow_three, invSqrtTwo_pow_four,
      Complex.I_sq])
    all_goals (try ring_nf)
    all_goals (try simp only [and_self])))

/-! ## The rows -/

-- source: papers/tensor_network_simulation/
-- Rudolph_2025_pauli_propagation_framework_2505.21606 paragraph:hb2de6d2ffcac
-- row: agreement
/-- **H.** The transfer matrix of H on one bit, from its definition, is the symplectic swap of X
and Z (`hadamardAt 0`, `FTQCLib/Gates/Hadamard.lean`) with the sign `(−1)^{a·b}` of the real
convention: `R(Z, X) = R(X, Z) = R(I, I) = 1`, `R(XZ, XZ) = −1` (`H XZ H = ZX = −XZ`, the source's
`H[Y] = −Y`), and `0` elsewhere. -/
theorem row_ptm_hadamard (P Q : Pauli 1) :
    ptm (channelBranch transferHadamard transferNone 0) P Q
      = if P = FTQCLib.Gates.hadamardAt 0 Q then signOf (Q.X 0 * Q.Z 0) else 0 := by
  rw [hadamardAt_one]
  rcases pauli_one_cases P with rfl | rfl | rfl | rfl <;>
  rcases pauli_one_cases Q with rfl | rfl | rfl | rfl <;>
  · rw [ptm_branch_apply]
    entry_eval

-- row: agreement
/-- **The bit flip at `p = ½`.** Conditioning on X with the outcome unread, `ρ ↦ ½ρ + ½XρX`: in
the order `(I, X, Z, XZ)`, χ's diagonal is `(½, ½, 0, 0)` and the transfer matrix's diagonal is
`(1, 1, 0, 0)`, the eigenvalues `1 − 2p` at Z and XZ. -/
theorem row_bitFlip :
    ![chi transferBitFlip transferUnread 0 transferPauliI transferPauliI,
        chi transferBitFlip transferUnread 0 transferPauliX transferPauliX,
        chi transferBitFlip transferUnread 0 transferPauliZ transferPauliZ,
        chi transferBitFlip transferUnread 0 transferPauliXZ transferPauliXZ]
      = ![2⁻¹, 2⁻¹, 0, 0]
    ∧ ![ptm (channelBranch transferBitFlip transferUnread 0) transferPauliI transferPauliI,
        ptm (channelBranch transferBitFlip transferUnread 0) transferPauliX transferPauliX,
        ptm (channelBranch transferBitFlip transferUnread 0) transferPauliZ transferPauliZ,
        ptm (channelBranch transferBitFlip transferUnread 0) transferPauliXZ transferPauliXZ]
      = ![1, 1, 0, 0] := by
  simp only [chi_unread_apply _ le_rfl, ptm_branch_apply]
  constructor <;> entry_eval

/-- The unitary X's χ diagonal, `δ_X`. -/
private theorem chi_unitaryX_diag :
    chi transferUnitaryX transferNone 0 transferPauliI transferPauliI = 0
      ∧ chi transferUnitaryX transferNone 0 transferPauliX transferPauliX = 1
      ∧ chi transferUnitaryX transferNone 0 transferPauliZ transferPauliZ = 0
      ∧ chi transferUnitaryX transferNone 0 transferPauliXZ transferPauliXZ = 0 := by
  simp only [chi_none_apply _ le_rfl]
  entry_eval

/-- The unitary X's transfer-matrix diagonal, `(1, 1, −1, −1)`. -/
private theorem ptm_unitaryX_diag :
    ptm (channelBranch transferUnitaryX transferNone 0) transferPauliI transferPauliI = 1
      ∧ ptm (channelBranch transferUnitaryX transferNone 0) transferPauliX transferPauliX = 1
      ∧ ptm (channelBranch transferUnitaryX transferNone 0) transferPauliZ transferPauliZ = -1
      ∧ ptm (channelBranch transferUnitaryX transferNone 0) transferPauliXZ transferPauliXZ
        = -1 := by
  simp only [ptm_branch_apply]
  entry_eval

-- row: discriminating
/-- **The unitary X.** X as the word `H Z H`: χ's diagonal is `δ_X`, a distribution on `Pauli 1`,
and the transfer matrix's diagonal is `(1, 1, −1, −1)`, which is not one (its value at Z is
negative). A Pauli channel's distribution is χ's diagonal, not the transfer matrix's. -/
theorem row_unitaryX :
    ![chi transferUnitaryX transferNone 0 transferPauliI transferPauliI,
        chi transferUnitaryX transferNone 0 transferPauliX transferPauliX,
        chi transferUnitaryX transferNone 0 transferPauliZ transferPauliZ,
        chi transferUnitaryX transferNone 0 transferPauliXZ transferPauliXZ] = ![0, 1, 0, 0]
    ∧ ![ptm (channelBranch transferUnitaryX transferNone 0) transferPauliI transferPauliI,
        ptm (channelBranch transferUnitaryX transferNone 0) transferPauliX transferPauliX,
        ptm (channelBranch transferUnitaryX transferNone 0) transferPauliZ transferPauliZ,
        ptm (channelBranch transferUnitaryX transferNone 0) transferPauliXZ transferPauliXZ]
      = ![1, 1, -1, -1]
    ∧ IsPauliDistribution (fun P => (chi transferUnitaryX transferNone 0 P P).re)
    ∧ ¬ IsPauliDistribution
        (fun P => (ptm (channelBranch transferUnitaryX transferNone 0) P P).re) := by
  obtain ⟨c1, c2, c3, c4⟩ := chi_unitaryX_diag
  obtain ⟨r1, r2, r3, r4⟩ := ptm_unitaryX_diag
  refine ⟨by rw [c1, c2, c3, c4], by rw [r1, r2, r3, r4], ⟨fun P => ?_, ?_⟩, fun h => ?_⟩
  · rcases pauli_one_cases P with rfl | rfl | rfl | rfl <;> simp only [c1, c2, c3, c4] <;> norm_num
  · rw [sum_pauli_one]
    simp only [c1, c2, c3, c4]
    norm_num
  · have h3 : 0 ≤ (ptm (channelBranch transferUnitaryX transferNone 0) transferPauliZ
        transferPauliZ).re := h.1 transferPauliZ
    rw [r3] at h3
    norm_num at h3

-- row: discriminating
/-- **The identity at `n = 1`.** The Bell reading of the empty protocol at `I` is `√2`, where the
Pauli coefficient of its Kraus operator is `c(I) = 1`: the reading carries the factor `2^{n/2}` of
T49's unnormalised floor `δ_{x = y}`, and is not the coefficient itself. -/
theorem row_identity_bellRead :
    amp (bellRead transferIdentity transferNone)
        (Fin.append (Fin.append (symplecticBits transferPauliI) 0) 0) = (Real.sqrt 2 : ℂ)
    ∧ pauliCoeff (krausOp transferIdentity transferNone 0 0) transferPauliI = 1
    ∧ amp (bellRead transferIdentity transferNone)
        (Fin.append (Fin.append (symplecticBits transferPauliI) 0) 0)
      ≠ pauliCoeff (krausOp transferIdentity transferNone 0 0) transferPauliI := by
  have hBell : amp (bellRead transferIdentity transferNone)
      (Fin.append (Fin.append (symplecticBits transferPauliI) 0) 0) = (Real.sqrt 2 : ℂ) := by
    rw [bellRead_none _ le_rfl]
    simp (config := {decide := true}) [dilation_none, transferPauliI, kraus_identity,
      signOf_zero, invSqrtTwo]
    have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
      norm_num
    field_simp
    rw [sqrt_two_sq_complex]
    norm_num
  have hCoeff : pauliCoeff (krausOp transferIdentity transferNone 0 0) transferPauliI = 1 := by
    unfold pauliCoeff krausOp
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def, sum_bits_one, dilation_none, transferPauliI, pauliMatrix_apply,
      Matrix.cons_val_zero]
    simp (config := {decide := true}) [kraus_identity, signOf_zero]
    norm_num
  refine ⟨hBell, hCoeff, ?_⟩
  rw [hBell, hCoeff]
  intro h
  have h2 := congrArg (fun z : ℂ => z ^ 2) h
  simp only [sqrt_two_sq_complex, one_pow] at h2
  norm_num at h2

/-- Z-conditioning's χ with the outcome unread: `(½, 0, ½, 0)` on the diagonal. -/
private theorem chi_zCondition_diag :
    chi transferZCondition transferUnread 0 transferPauliI transferPauliI = 2⁻¹
      ∧ chi transferZCondition transferUnread 0 transferPauliX transferPauliX = 0
      ∧ chi transferZCondition transferUnread 0 transferPauliZ transferPauliZ = 2⁻¹
      ∧ chi transferZCondition transferUnread 0 transferPauliXZ transferPauliXZ = 0 := by
  simp only [chi_unread_apply _ le_rfl]
  entry_eval

-- row: agreement
/-- **Z-conditioning with the outcome unread.** χ is zero off the diagonal and `(½, 0, ½, 0)` on
it, and the branch is the Pauli channel `ρ ↦ Σ_P χ(P, P) P ρ P†`, `½ρ + ½ZρZ`, computed from T49's
`channel`: the Pauli channel's distribution is χ's diagonal. -/
theorem row_zCondition_pauliChannel :
    (∀ P Q : Pauli 1, P ≠ Q → chi transferZCondition transferUnread 0 P Q = 0)
    ∧ ![chi transferZCondition transferUnread 0 transferPauliI transferPauliI,
        chi transferZCondition transferUnread 0 transferPauliX transferPauliX,
        chi transferZCondition transferUnread 0 transferPauliZ transferPauliZ,
        chi transferZCondition transferUnread 0 transferPauliXZ transferPauliXZ]
      = ![2⁻¹, 0, 2⁻¹, 0]
    ∧ ∀ ρ : Matrix (Fin 1 → ZMod 2) (Fin 1 → ZMod 2) ℂ,
        channelBranch transferZCondition transferUnread 0 ρ
          = ∑ P : Pauli 1, chi transferZCondition transferUnread 0 P P
              • (pauliMatrix P * ρ * (pauliMatrix P)ᴴ) := by
  obtain ⟨c1, c2, c3, c4⟩ := chi_zCondition_diag
  refine ⟨fun P Q hPQ => ?_, by rw [c1, c2, c3, c4], fun ρ => ?_⟩
  · rcases pauli_one_cases P with rfl | rfl | rfl | rfl <;>
    rcases pauli_one_cases Q with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hPQ
    | (rw [chi_unread_apply _ le_rfl]; entry_eval)
  · rw [sum_pauli_one, c1, c2, c3, c4]
    funext w w'
    rw [bits_one w, bits_one w']
    unfold channelBranch channel
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def, smul_eq_mul, sum_bits_one, dilation_unread, transferPauliI,
      transferPauliX, transferPauliZ, transferPauliXZ, pauliMatrix_apply, Matrix.cons_val_zero]
    rcases zmod_two_dichotomy (w 0) with hw | hw <;>
    rcases zmod_two_dichotomy (w' 0) with hw' | hw' <;>
    · rw [hw, hw']
      simp (config := {decide := true}) [kraus_zCondition, signOf_zero, signOf_one]
      try ring

/-- The T gate's χ and transfer-matrix entries, from their definitions. -/
private theorem t_entries :
    chi transferT transferNone 0 transferPauliI transferPauliZ = 4⁻¹ * (2 * Complex.I * invSqrtTwo)
      ∧ ∀ Q : Pauli 1, ptm (channelBranch transferT transferNone 0) Q Q
        = ∑ P : Pauli 1, chi transferT transferNone 0 P P * signOf (omega P Q) := by
  refine ⟨?_, fun Q => ?_⟩
  · rw [chi_none_apply _ (by norm_num)]
    entry_eval
  · rw [sum_pauli_one]
    simp only [chi_none_apply _ (by norm_num : 1 ≤ 3), omega, Fin.sum_univ_one]
    rcases pauli_one_cases Q with rfl | rfl | rfl | rfl <;>
    · rw [ptm_branch_apply]
      entry_eval

-- row: discriminating
/-- **The T gate.** χ is not diagonal, `χ(I, Z) = i/(2√2) ≠ 0`, so the T gate's channel is no
Pauli channel; and its transfer-matrix diagonal is still `2 Ŵ` of χ's diagonal at every `Q`,
`R(Q, Q) = Σ_P χ(P, P)(−1)^{ω(P, Q)}`, both sides computed from their definitions. -/
theorem row_tGate :
    chi transferT transferNone 0 transferPauliI transferPauliZ ≠ 0
    ∧ ∀ Q : Pauli 1, ptm (channelBranch transferT transferNone 0) Q Q
        = (2 : ℂ) ^ 1 * walsh2n (fun P => chi transferT transferNone 0 P P) Q := by
  obtain ⟨hIZ, hdiag⟩ := t_entries
  refine ⟨?_, fun Q => ?_⟩
  · rw [hIZ]
    exact mul_ne_zero (by norm_num)
      (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) invSqrtTwo_ne_zero)
  · rw [hdiag, walsh2n, pow_one, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
    exact Finset.sum_congr rfl fun P _ => mul_comm _ _

-- row: inhabitation
/-- **The bit flip's χ diagonal is a distribution (inhabitation).** The headline
`chi_diag_isDistribution`'s hypotheses — a protocol at a positive precision, read through an
equivalence with no read outcome bit — hold together at the bit flip `transferBitFlip` read
through `transferUnread` (`r = 0`, `m = 1`), and the headline then gives a concrete probability
distribution whose values are χ's diagonal, in the ring. -/
theorem row_bitFlip_isDistribution :
    ∃ d : Pauli 1 → ℝ, IsPauliDistribution d ∧
      ∀ P : Pauli 1, chi transferBitFlip transferUnread 0 P P = d P
        ∧ (d P : ℂ) ∈ dyadicCyclotomicRing :=
  chi_diag_isDistribution transferBitFlip transferUnread le_rfl

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.walsh2n_eq_runAmp' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms walsh2n_eq_runAmp

/-- info: 'FTQCLib.Frame.Walkthrough.doubledBit_castAdd_ne_natAdd' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms doubledBit_castAdd_ne_natAdd

/-- info: 'FTQCLib.Frame.Walkthrough.bellRead_choi_eq_pauliCoeff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bellRead_choi_eq_pauliCoeff

/-- info: 'FTQCLib.Frame.Walkthrough.channel_eq_chi_sum' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms channel_eq_chi_sum

/-- info: 'FTQCLib.Frame.Walkthrough.ptm_eq_chi_basis' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ptm_eq_chi_basis

/-- info: 'FTQCLib.Frame.Walkthrough.ptm_diag_eq_walsh_chi_diag' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ptm_diag_eq_walsh_chi_diag

/-- info: 'FTQCLib.Frame.Walkthrough.pauliChannel_iff_chi_diagonal' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pauliChannel_iff_chi_diagonal

/-- info: 'FTQCLib.Frame.Walkthrough.chi_diag_isDistribution' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chi_diag_isDistribution

/-! ## The mutants -/

-- mutant: ptm_diag_conclusion | FTQCLib/Carrier/PauliTransfer.lean | (2 : ℂ) ^ n * walsh2n
--   | (3 : ℂ) ^ n * walsh2n
-- The diagonal duality's `2^n`, the conclusion `ptm_diag_eq_walsh_chi_diag` establishes: changing
-- it to `3^n` is caught by `row_tGate`, which computes both sides of the duality from their
-- definitions at `n = 1`.

-- mutant: chi_diag_isDistribution_sum | FTQCLib/Carrier/PauliTransfer.lean
--   | ∑ P : Pauli n, d P = 1
--   | ∑ P : Pauli n, d P = 2
-- `chi_diag_isDistribution`'s conclusion that the diagonal sums to `1`: changing the target sum is
-- caught by `row_zCondition_pauliChannel`, whose χ diagonal `(½, 0, ½, 0)` sums to `1`, not `2`,
-- computed from `chi`'s definition, not through the headline.

end FTQCLib.Frame.Walkthrough

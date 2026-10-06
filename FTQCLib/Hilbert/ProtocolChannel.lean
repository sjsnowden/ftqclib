/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.BranchSoundness
import FTQCLib.Carrier.HInject
import FTQCLib.Carrier.RemoteCH
import FTQCLib.Carrier.UnreadBits

/-!
# The non-selective channel of a protocol, and the capstones in Hilbert space

T21 (`docs/TARGETS.md`), as corrected on 2026-10-02 (`docs/STEPS.md`, entry 2026-10-02l): the
non-selective result of a protocol is the trace-preserving Kraus sum `ρ ↦ Σ_o K_o ρ K_o†` on
Mathlib's `Matrix`, the Lüders channel only in the one-letter case, and the capstones T15 and T16
are channel equalities `ρ ↦ G ρ G†`. The `K_o` are T17's `kraus p o`
(`Hilbert/ProtocolSemantics.lean`), the matrices of `(I ⊗ ⟨o|) ⟦p⟧`, with
`Σ_o K_o† K_o = 1` (`kraus_sum_eq_one`).

**The weights** (`kraus_weights_sum`). `Σ_o ‖K_o ψ‖² = ‖ψ‖²` for **every** vector `ψ`, each norm
the sum of `Complex.normSq` over the words, as T14's `branchWeight` and `ampNormSq` are. T14's
`branch_weights_sum` read through T20's `branch_eq_kraus` gives the identity only at `ψ = amp S`
for a carrier state `S` at the protocol's precision, and a quadratic identity on a spanning set does
not extend by linearity; so the statement is for every `ψ`, and the carrier reading is its instance
at `amp S` (`docs/fidelity/T21.md`, Claim 3).

**The channel** (`nonselective`). The outcomes not read: `nonselective p ρ = Σ_o K_o ρ K_o†`, the
Kraus sum of T17's family (`krausChannel`). Mathlib has no quantum channel, so trace preservation
is stated here as `Matrix.trace (nonselective p ρ) = Matrix.trace ρ` for every `ρ`
(`nonselective_tracePreserving`). **Nothing here claims unitality**: with feed-forward the channel
need not be unital. Conditioning on `Z₀`, then CNOT from the outcome bit to bit 0, has
`K₀ = |0⟩⟨0|`, `K₁ = |0⟩⟨1|` and is the reset `ρ ↦ tr(ρ)|0⟩⟨0|`, which takes `I/2` to `|0⟩⟨0|`
(T21.2's row `R2`).

**The Lüders case** (`nonselective_condition_eq_luders`), the one-letter case only. The term
begins with its one conditioning letter, on a signed Pauli `P` of the data bits, and continues with
a word whose letters name either data bits only or the outcome bit only: `liftData 1 w₁`, a word
`w₁` on the data bits, then `liftUnread n w₂`, a word `w₂` on the outcome bit alone. Its channel is
the Lüders channel `Σ_b Π_b ρ Π_b` of `P`'s Born projectors followed by `w₁`'s unitary `U`:
`ρ ↦ U (Σ_b Π_b ρ Π_b) U†`. Two readings are excluded because they are false
(`docs/fidelity/T21.md`, Claims 9 and 10, computed there):

* a word before the letter: H on bit 0, then conditioning on `Z₀`, takes `|+⟩⟨+|` to `|0⟩⟨0|`,
  while the Lüders channel of `Z` followed by H takes it to `I/2`;
* a later letter naming the outcome bit with a data bit, even with the outcome as no letter's
  control: conditioning on `X₀`, then CNOT from bit 0 into the outcome bit, takes `|+⟩⟨+|` to
  `I/2`, while the Lüders channel of `X` fixes it.

A word whose letters each name data bits only or the outcome bit only, in any interleaving, is
`liftData 1 w₁ ++ liftUnread n w₂` up to reordering letters on disjoint bits, which commute; a
diagonal letter whose exponent is a sum of a data part and an outcome part is two such letters.

**The capstones** (`hInject_channel_eq`, `remoteCH_channel_eq`). The Kraus operators are those of
the capstone, not of the bare protocol term: T17's `kraus (hInjectProtocol m j) b` acts on `n + 1`
bits with rank `2^n`, so it is no scalar multiple of a unitary (`docs/fidelity/T21.md`, Claim 17).
The capstone is the composite T15 and T16 describe, with the ancillas prepared **normalised**
(`plusAncilla`, `ψ ↦ ψ ⊗ |+⟩`, an isometry, where T15's and T16's `appendFreeBit` keeps the
scale, D3, and gives `|0⟩ + |1⟩ = √2|+⟩`), then the protocol at an outcome string `o` (`kraus`),
then T15's or T16's processing of the branch, the discarded bits read at a string `d`:

* **H inject** (`hInjectKraus m j (o, d)`), on the register's `n` bits: one `|+⟩` ancilla; the
  protocol's `K_o`; H on the measured qubit `j`; the swap of bit `j` and the ancilla, bit `n`; the
  measured qubit, now bit `n`, read at `d`. `G` is H on bit `j` (`hadamardGate j`), and the scalar
  of `(o, d)` is `1/√2` when `d = o 0` and `0` otherwise.
* **Remote CH** (`remoteCHKraus k hk c t (o, d)`), on the register's `n` bits: two `|+⟩`
  ancillas, the ebit's halves `A₁` (bit `n`) and `B₁` (bit `n + 1`); the protocol's `K_o` at
  `o = ![s, u]`; `A₁` and `B₁` read at `d = ![d 0, d 1]`. `G` is controlled-H from `c` to `t`
  (`controlledHadamardGate c t`), and the scalar is `1/2` when `d = o` and `0` otherwise.

Each theorem states that every Kraus operator is its scalar times `G`, that the scalars' squared
moduli sum to one, and that the channel is `ρ ↦ G ρ G†`. The zero operators are the scalar `0`:
the discarded bits are fixed in each branch (`docs/fidelity/T21.md`, the seventh point). These are
T15's `hInject_correct` and T16's `remoteCH_correct` carried across T17 to T20: no new
mathematics, which is the sense of "corollaries".

## Main definitions

* `krausChannel` — the channel `ρ ↦ Σ_i K_i ρ K_i†` of a family of matrices.
* `nonselective` — the protocol's non-selective channel, `krausChannel` of T17's `kraus p`.
* `GateLetter.liftData`, `liftData` — a letter or word on `n` bits, read on the first `n` of
  `n + k` bits; the counterpart of `liftUnread` for the data bits.
* `plusAncilla` — `ψ ↦ ψ ⊗ |+⟩`, the ancilla normalised, a new last bit.
* `controlledHadamardGate` — controlled-H on `QubitSpace`, from the Hilbert side's `hadamardGate`.
* `hInjectKraus`, `remoteCHKraus` — the capstones' Kraus families.

## Main results

* `kraus_weights_sum` — `Σ_o ‖K_o ψ‖² = ‖ψ‖²` for every `ψ` (proved at T21.3.1).
* `nonselective_tracePreserving` — `tr (nonselective p ρ) = tr ρ` (proved at T21.3.1).
* `nonselective_condition_eq_luders` — the one-letter case is the Lüders channel followed by the
  data word's unitary (proved at T21.3.1).
* `hInject_channel_eq`, `remoteCH_channel_eq` — every Kraus operator of the capstone is a scalar
  multiple of its gate `G`, the scalars' squared moduli summing to one, and the channel is
  `ρ ↦ G ρ G†` (proved at T21.3.2).

## Implementation notes

* Matrices are indexed by words, `Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ`, the type of T17's
  `kraus p o`; a linear map on `QubitSpace` enters through `LinearMap.toMatrix'`. The Born
  projector `Π_b` is `LinearMap.toMatrix' (bornProjection P b)`, Hermitian, so `Π_b ρ Π_b` is
  `Π_b ρ Π_b†`.
* `G` is the Hilbert side's own gate in both capstones, not the frame's referee: `hadamardGate j`,
  and `controlledHadamardGate c t`, which is the identity where bit `c` is `0` and `hadamardGate t`
  where it is `1`. That they agree with `walshTransform` and `controlledHAmp` is T18's
  `runAmp_eq_wordGate` and is for the proof.
* H inject's precision `m` is any `m ≥ 1`: the CZ letter is `2^{m−1}·x_j·x_n`, which is the phase
  `π·x_j·x_n` exactly when `m ≥ 1`. Remote CH's precision is any `k ≥ 3`, which T08's word needs.
  The register's own precision does not enter: the channel is a map on all matrices.
* `GateLetter.liftData` is in `FTQCLib.Frame.Walkthrough`, beside `GateLetter.liftUnread`
  (`Carrier/UnreadBits.lean`), whose home it shares; it is written here because this step may
  write only this module. `PauliTransfer.lean` has the same map privately (`castAddLetter`).
* The proof route (`docs/fidelity/T21.md`, Claims 16 to 18), as proved at T21.3.2: T20's
  `interpretAmp_eq_hilbertSem`, of which `branch_eq_kraus` is the evaluation at `o`, holds for
  every function, so `L ψ = c G ψ` is computed on every `ψ` from the frame's closed forms and no
  spanning step is needed. For remote CH the closed form is the public
  `interpretAmp_remoteCHProtocol`, with the vanishing off `d = o` restated from `RemoteCH.lean`;
  for H inject the closed form `injectRead_eq` and the Walsh step after it are private in
  `HInject.lean` and are restated here, the swap lemma extended to the zero operators. The
  scalars' sum is a count, and the channel follows from it (`krausChannel_eq_of_smul`).
* No `-- source:` citation: T21's section in `docs/TARGETS.md` names no corpus papers.

## References

* E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, arXiv:quant-ph/9604034:
  the reduced density matrix `Σ_a A_a ρ A_a†` with `Σ_a A_a† A_a = I`.
* G. Lüders, *Über die Zustandsänderung durch den Meßprozeß*, Ann. Phys. (Leipzig) 8, 322–328
  (1951), equation (8): `Z′ = Σ_k P_k Z P_k`; translated by K. A. Kirkpatrick,
  arXiv:quant-ph/0403007.
* X. Zhou, D. W. Leung and I. L. Chuang, arXiv:quant-ph/0002039, and J. Eisert, K. Jacobs,
  P. Papadopoulos and M. B. Plenio, arXiv:quant-ph/0005101: the capstones' circuits, cited in
  `Carrier/HInject.lean` and `Carrier/RemoteCH.lean`.
-/

namespace FTQCLib.Frame.Walkthrough

/-- **A letter on the data bits**: a letter on `n` bits, read on `n + k` bits at the first `n`: H
and CNOT at the same bits, a diagonal exponent with its variables renamed to the first `n`. -/
noncomputable def GateLetter.liftData {n m : ℕ} (k : ℕ) : GateLetter n m → GateLetter (n + k) m
  | .hadamard i => .hadamard (Fin.castAdd k i)
  | .diagonal D => .diagonal (MvPolynomial.rename (Fin.castAdd k) D)
  | .cnot i j hij => .cnot (Fin.castAdd k i) (Fin.castAdd k j)
      fun h => hij (Fin.castAdd_injective n k h)

/-- **A word on the data bits**: a word on `n` bits, read on the first `n` of `n + k` bits, letter
by letter. -/
noncomputable def liftData {n m : ℕ} (k : ℕ) (W : GateWord n m) : GateWord (n + k) m :=
  W.map (GateLetter.liftData k)

end FTQCLib.Frame.Walkthrough

namespace FTQCLib.Hilbert

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Frame.Walkthrough
open scoped Matrix

variable {m n : ℕ}

/-! ## The channel of a Kraus family -/

/-- **The channel of a family of matrices** `ρ ↦ Σ_i K_i ρ K_i†`. -/
noncomputable def krausChannel {ι α β : Type*} [Fintype ι] [Fintype α] (K : ι → Matrix β α ℂ)
    (ρ : Matrix α α ℂ) : Matrix β β ℂ :=
  ∑ i, K i * ρ * (K i)ᴴ

/-- **The non-selective channel of a protocol**: the outcomes not read, `ρ ↦ Σ_o K_o ρ K_o†`, the
Kraus sum of T17's family `kraus p`, over every outcome string. -/
noncomputable def nonselective {k : ℕ} (p : Protocol m n k)
    (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  krausChannel (kraus p) ρ

/-- The non-selective channel is the Kraus sum. -/
theorem nonselective_apply {k : ℕ} (p : Protocol m n k)
    (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    nonselective p ρ = ∑ o : Fin k → ZMod 2, kraus p o * ρ * (kraus p o)ᴴ :=
  rfl

/-! ## The weights and trace preservation -/

/-- A sum of squared moduli is the dot product of the conjugate with the vector. -/
private theorem ofReal_sum_normSq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    ((∑ y, Complex.normSq (v y) : ℝ) : ℂ) = star v ⬝ᵥ v := by
  rw [Complex.ofReal_sum, dotProduct]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/-- **The weights of all outcome strings sum to the input's squared norm**:
`Σ_o ‖K_o ψ‖² = ‖ψ‖²` for every vector `ψ`, each squared norm the sum of `Complex.normSq` over the
words. At `ψ = amp S`, for a carrier state `S` at the protocol's precision, the left side is T14's
`Σ_o branchWeight p S o` (T20's `branch_eq_kraus`) and the right side `ampNormSq S`: T14's
`branch_weights_sum`. Proved at T21.3.1. -/
theorem kraus_weights_sum {k : ℕ} (p : Protocol m n k) (ψ : QubitSpace n) :
    ∑ o : Fin k → ZMod 2, ∑ y : Fin n → ZMod 2, Complex.normSq ((kraus p o *ᵥ ψ) y)
      = ∑ y : Fin n → ZMod 2, Complex.normSq (ψ y) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, ofReal_sum_normSq]
  have h : ∀ o : Fin k → ZMod 2,
      ((∑ y : Fin n → ZMod 2, Complex.normSq ((kraus p o *ᵥ ψ) y) : ℝ) : ℂ)
        = star ψ ⬝ᵥ (((kraus p o)ᴴ * kraus p o) *ᵥ ψ) := fun o => by
    rw [ofReal_sum_normSq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rw [Finset.sum_congr rfl fun o _ => h o, ← dotProduct_sum, ← Matrix.sum_mulVec,
    kraus_sum_eq_one, Matrix.one_mulVec]

/-- **The non-selective channel is trace preserving**: `tr (Σ_o K_o ρ K_o†) = tr ρ` for every
matrix `ρ`. Proved at T21.3.1. -/
theorem nonselective_tracePreserving {k : ℕ} (p : Protocol m n k)
    (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    (nonselective p ρ).trace = ρ.trace := by
  rw [nonselective, krausChannel, Matrix.trace_sum]
  have h : ∀ o : Fin k → ZMod 2, (kraus p o * ρ * (kraus p o)ᴴ).trace
      = ((kraus p o)ᴴ * kraus p o * ρ).trace := fun o => by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun o _ => h o, ← Matrix.trace_sum, ← Finset.sum_mul, kraus_sum_eq_one,
    Matrix.one_mul]

/-! ## The one-letter case: Lüders -/

/-! ### Private: the one-letter term's Kraus operators -/

/-- A letter on the data bits acts on the slice at each outcome word as the letter itself. -/
private theorem letterAmp_liftData {N M K : ℕ} (l : GateLetter N M)
    (F : (Fin (N + K) → ZMod 2) → ℂ) (t : Fin K → ZMod 2) :
    (fun v => letterAmp (l.liftData K) F (Fin.append v t))
      = letterAmp l (fun v => F (Fin.append v t)) := by
  funext v
  cases l with
  | hadamard i =>
    change walshTransform (Fin.castAdd K i) F (Fin.append v t)
      = walshTransform i (fun v => F (Fin.append v t)) v
    unfold walshTransform
    rw [update_append_castAdd, update_append_castAdd, Fin.append_left]
  | diagonal D =>
    change charOf M (DiagPhase.eval (MvPolynomial.rename (Fin.castAdd K) D) (Fin.append v t))
        * F (Fin.append v t)
      = charOf M (DiagPhase.eval D v) * F (Fin.append v t)
    rw [eval_rename_castAdd]
  | cnot i j hij =>
    change F (DiagPhase.cnotBitMap (Fin.castAdd K i) (Fin.castAdd K j) (Fin.append v t))
      = F (Fin.append (DiagPhase.cnotBitMap i j v) t)
    unfold DiagPhase.cnotBitMap
    rw [Fin.append_left, Fin.append_left, update_append_castAdd]

/-- A word on the data bits acts on the slice at each outcome word as the word itself
(`PauliTransfer.lean`'s private `runAmp_castAddWord`, restated). -/
private theorem runAmp_liftData {N M K : ℕ} (W : GateWord N M)
    (F : (Fin (N + K) → ZMod 2) → ℂ) (v : Fin N → ZMod 2) (t : Fin K → ZMod 2) :
    runAmp (liftData K W) F (Fin.append v t) = runAmp W (fun v' => F (Fin.append v' t)) v := by
  induction W generalizing F with
  | nil => rfl
  | cons l W ih =>
    change runAmp (liftData K W) (letterAmp (l.liftData K) F) (Fin.append v t) = _
    rw [ih, letterAmp_liftData, runAmp_cons]

/-- The binary lift of `Fin.append x u`, read at the last coordinates, is the lift of `u`
(`UnreadBits.lean`'s private `liftBinary_append_comp_natAdd`, restated). -/
private theorem liftBinary_comp_natAdd_append {N K M : ℕ} (x : Fin N → ZMod 2)
    (u : Fin K → ZMod 2) :
    (DiagPhase.liftBinary (m := M) (Fin.append x u) ∘ Fin.natAdd N) = DiagPhase.liftBinary u := by
  funext i
  change (((Fin.append x u) (Fin.natAdd N i)).val : ZMod (2 ^ M)) = ((u i).val : ZMod (2 ^ M))
  rw [Fin.append_right]

/-- A letter on the last bits acts on the vector at each data word as the letter itself. -/
private theorem letterAmp_liftUnread {N K M : ℕ} (g : GateLetter K M)
    (F : (Fin (N + K) → ZMod 2) → ℂ) (x : Fin N → ZMod 2) :
    (fun u => letterAmp (g.liftUnread N) F (Fin.append x u))
      = letterAmp g (fun u => F (Fin.append x u)) := by
  funext u
  cases g with
  | hadamard i =>
    change walshTransform (Fin.natAdd N i) F (Fin.append x u)
      = walshTransform i (fun u => F (Fin.append x u)) u
    unfold walshTransform
    rw [update_append_natAdd, update_append_natAdd, Fin.append_right]
  | diagonal D =>
    change charOf M (DiagPhase.eval (MvPolynomial.rename (Fin.natAdd N) D) (Fin.append x u))
        * F (Fin.append x u)
      = charOf M (DiagPhase.eval D u) * F (Fin.append x u)
    rw [DiagPhase.eval, DiagPhase.eval, MvPolynomial.eval_rename, liftBinary_comp_natAdd_append]
  | cnot i j hij =>
    change F (DiagPhase.cnotBitMap (Fin.natAdd N i) (Fin.natAdd N j) (Fin.append x u))
      = F (Fin.append x (DiagPhase.cnotBitMap i j u))
    unfold DiagPhase.cnotBitMap
    rw [Fin.append_right, Fin.append_right, update_append_natAdd]

/-- A word on the last bits acts on the vector at each data word as the word itself
(`UnreadBits.lean`'s private `unreadVector_runAmp_liftUnread`, restated). -/
private theorem runAmp_liftUnread {N K M : ℕ} (W : GateWord K M)
    (F : (Fin (N + K) → ZMod 2) → ℂ) (x : Fin N → ZMod 2) (u : Fin K → ZMod 2) :
    runAmp (liftUnread N W) F (Fin.append x u) = runAmp W (fun u' => F (Fin.append x u')) u := by
  induction W generalizing F with
  | nil => rfl
  | cons g W ih =>
    change runAmp (liftUnread N W) (letterAmp (g.liftUnread N) F) (Fin.append x u) = _
    rw [ih, letterAmp_liftUnread, runAmp_cons]

/-- The inner product with a basis vector reads the function at its word. -/
private theorem inner_toQState_single {N : ℕ} (a : Fin N → ZMod 2) (f : QubitSpace N) :
    inner ℂ (toQState (Pi.single a (1 : ℂ) : QubitSpace N)) (toQState f) = f a := by
  rw [PiLp.inner_apply, Finset.sum_eq_single a]
  · rw [toQState_apply, toQState_apply, Pi.single_eq_same, RCLike.inner_apply, map_one, mul_one]
  · intro v _ hv
    rw [toQState_apply, Pi.single_eq_of_ne hv, RCLike.inner_apply, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A Born projector at a real sign is symmetric. -/
private theorem bornProjector_symm {N : ℕ} (Q : Pauli N) {ε : ℂ} (hε : starRingEnd ℂ ε = ε)
    (x y : QState N) :
    inner ℂ (bornProjector Q ε x) y = inner ℂ x (bornProjector Q ε y) := by
  rw [bornProjector, LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left,
    inner_smul_right, LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_right,
    LinearMap.id_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    inner_smul_left, inner_smul_right, hε, pauliHermitian_isSymmetric Q x y]
  have hhalf : starRingEnd ℂ (2⁻¹ : ℂ) = 2⁻¹ := by
    rw [map_inv₀, map_ofNat]
  rw [hhalf]

/-- `bornProjection` read through `toQState` (`ProtocolSemantics.lean`'s private
`toQState_bornProjection`, restated). -/
private theorem toQState_bornProjection_apply {N : ℕ} (P : SignedPauli N) (b : ZMod 2)
    (ψ : QubitSpace N) :
    toQState (bornProjection P b ψ)
      = bornProjector P.pauli ((-1 : ℂ) ^ (P.sign.val + b.val)) (toQState ψ) := by
  rw [bornProjection, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- The Born projector's matrix is Hermitian. -/
private theorem conjTranspose_bornProjection {N : ℕ} (P : SignedPauli N) (b : ZMod 2) :
    (LinearMap.toMatrix' (bornProjection P b))ᴴ = LinearMap.toMatrix' (bornProjection P b) := by
  have hε : starRingEnd ℂ ((-1 : ℂ) ^ (P.sign.val + b.val)) = (-1 : ℂ) ^ (P.sign.val + b.val) := by
    rw [map_pow, map_neg, map_one]
  ext i j
  rw [Matrix.conjTranspose_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply,
    ← inner_toQState_single j (bornProjection P b _),
    ← inner_toQState_single i (bornProjection P b _), toQState_bornProjection_apply,
    toQState_bornProjection_apply, ← bornProjector_symm _ hε, ← inner_conj_symm]
  exact star_star _

/-- `⟦P⟧ φ` at the word `(u, t)` is the Born projector at the outcome `t 0`, at `u`
(`ProtocolSemantics.lean`'s private `conditionIsometry_append`, restated). -/
private theorem conditionIsometry_apply_append {N : ℕ} (P : SignedPauli N) (φ : QubitSpace N)
    (u : Fin N → ZMod 2) (t : Fin 1 → ZMod 2) :
    conditionIsometry P φ (Fin.append u t) = bornProjection P (t 0) φ u := by
  rw [conditionIsometry, LinearMap.coe_sum, Finset.sum_apply, Finset.sum_apply,
    Finset.sum_eq_single (t 0)]
  · rw [LinearMap.comp_apply]
    change (if Fin.append u t ∘ Fin.natAdd N = fun _ => t 0 then
      bornProjection P (t 0) φ (Fin.append u t ∘ Fin.castAdd 1) else 0) = _
    rw [append_comp_natAdd, append_comp_castAdd,
      if_pos (funext fun i => by rw [Subsingleton.elim i 0])]
  · intro b _ hb
    rw [LinearMap.comp_apply]
    change (if Fin.append u t ∘ Fin.natAdd N = fun _ => b then
      bornProjection P b φ (Fin.append u t ∘ Fin.castAdd 1) else 0) = 0
    rw [if_neg]
    intro h
    rw [append_comp_natAdd] at h
    exact hb (congrFun h 0).symm
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A word on one bit has a unitary matrix: T17's Kraus sum for the term that is the word alone. -/
private theorem wordGate_one_unitary (w : GateWord 1 m) :
    (LinearMap.toMatrix' (wordGate w))ᴴ * LinearMap.toMatrix' (wordGate w) = 1 := by
  have h := kraus_sum_eq_one ((Protocol.nil : Protocol m 1 0).word w)
  rw [Fintype.sum_unique] at h
  have hk : ∀ o, kraus ((Protocol.nil : Protocol m 1 0).word w) o
      = LinearMap.toMatrix' (wordGate w) := fun o => by
    rw [kraus, hilbertSem_word, hilbertSem_nil, LinearMap.comp_id]
    congr 1
    refine LinearMap.ext fun ψ => funext fun y => ?_
    rw [LinearMap.comp_apply]
    change wordGate w ψ (Fin.append y o) = wordGate w ψ y
    rw [Fin.append_right_nil y o rfl]
    rfl
  rw [hk] at h
  exact h

/-- The one-letter term's Kraus operator at `o` is `Σ_t V_{o t} U Π_{t 0}`, `V` the matrix of the
outcome bit's word and `U` that of the data word. -/
private theorem kraus_condition_word (P : SignedPauli n)
    (hP : yWeight P.pauli % 2 = 1 → 2 ≤ m) (w₁ : GateWord n m) (w₂ : GateWord 1 m)
    (o : Fin 1 → ZMod 2) :
    kraus (((Protocol.nil : Protocol m n 0).condition P hP).word
        (liftData 1 w₁ ++ liftUnread n w₂)) o
      = ∑ t : Fin 1 → ZMod 2, LinearMap.toMatrix' (wordGate w₂) o t •
          (LinearMap.toMatrix' (wordGate w₁) * LinearMap.toMatrix' (bornProjection P (t 0))) := by
  have hL : evalOutcome n o ∘ₗ hilbertSem (((Protocol.nil : Protocol m n 0).condition P hP).word
        (liftData 1 w₁ ++ liftUnread n w₂))
      = ∑ t : Fin 1 → ZMod 2, LinearMap.toMatrix' (wordGate w₂) o t •
          (wordGate w₁ ∘ₗ bornProjection P (t 0)) := by
    refine LinearMap.ext fun ψ => funext fun y => ?_
    rw [hilbertSem_word, hilbertSem_condition, hilbertSem_nil, LinearMap.comp_id, wordGate_append,
      LinearMap.comp_apply]
    change wordGate (liftUnread n w₂) (wordGate (liftData 1 w₁) (conditionIsometry P ψ))
      (Fin.append y o) = _
    have hslice : (fun u => wordGate (liftData 1 w₁) (conditionIsometry P ψ) (Fin.append y u))
        = fun u : Fin 1 → ZMod 2 => wordGate w₁ (bornProjection P (u 0) ψ) y := by
      funext u
      rw [← runAmp_eq_wordGate (liftData 1 w₁), runAmp_liftData, runAmp_eq_wordGate w₁]
      exact congrFun (congrArg (wordGate w₁)
        (funext fun v => conditionIsometry_apply_append P ψ v u)) y
    rw [← runAmp_eq_wordGate (liftUnread n w₂), runAmp_liftUnread, runAmp_eq_wordGate w₂, hslice,
      ← LinearMap.toMatrix'_mulVec, LinearMap.coe_sum, Finset.sum_apply, Finset.sum_apply,
      Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, LinearMap.comp_apply]
  rw [kraus, hL, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, LinearMap.toMatrix'_comp]

/-- A Kraus family `K_i = Σ_t c_{i t} A_t` whose coefficient columns are orthonormal has the channel
of the family `A`. -/
private theorem krausChannel_sum_smul {ι τ α : Type*} [Fintype ι] [Fintype τ] [DecidableEq τ]
    [Fintype α] (c : ι → τ → ℂ) (A : τ → Matrix α α ℂ)
    (hc : ∀ t t', ∑ i, star (c i t') * c i t = if t' = t then 1 else 0) (ρ : Matrix α α ℂ) :
    krausChannel (fun i => ∑ t, c i t • A t) ρ = ∑ t, A t * ρ * (A t)ᴴ := by
  rw [krausChannel]
  have h1 : ∀ i, (∑ t, c i t • A t) * ρ * (∑ t', c i t' • A t')ᴴ
      = ∑ t, ∑ t', (star (c i t') * c i t) • (A t * ρ * (A t')ᴴ) := by
    intro i
    rw [Matrix.conjTranspose_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t' _ => ?_
    rw [Matrix.conjTranspose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_comm]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  have h2 : ∀ t', ∑ i, (star (c i t') * c i t) • (A t * ρ * (A t')ᴴ)
      = if t' = t then A t * ρ * (A t')ᴴ else 0 := by
    intro t'
    rw [← Finset.sum_smul, hc t t', ite_smul, one_smul, zero_smul]
  rw [Finset.sum_congr rfl fun t' _ => h2 t', Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_univ t)]

/-- **The one-letter case is the Lüders channel followed by the term's unitary.** The term begins
with one conditioning letter on a signed Pauli `P` of the `n` data bits, then a word `w₁` on the
data bits, then a word `w₂` on the outcome bit alone, so that no later letter names the outcome bit
together with a data bit. Its non-selective channel is `ρ ↦ U (Σ_b Π_b ρ Π_b) U†`, the Lüders
channel of `P`'s Born projectors `Π_b` followed by `w₁`'s unitary `U`; `w₂` acts on the traced
outcome register and drops out. Proved at T21.3.1. -/
theorem nonselective_condition_eq_luders (P : SignedPauli n)
    (hP : yWeight P.pauli % 2 = 1 → 2 ≤ m) (w₁ : GateWord n m) (w₂ : GateWord 1 m)
    (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    nonselective (((Protocol.nil : Protocol m n 0).condition P hP).word
        (liftData 1 w₁ ++ liftUnread n w₂)) ρ
      = LinearMap.toMatrix' (wordGate w₁) *
          (∑ b : ZMod 2, LinearMap.toMatrix' (bornProjection P b) * ρ *
            LinearMap.toMatrix' (bornProjection P b)) *
          (LinearMap.toMatrix' (wordGate w₁))ᴴ := by
  have hc : ∀ t t' : Fin 1 → ZMod 2, ∑ o, star (LinearMap.toMatrix' (wordGate w₂) o t')
      * LinearMap.toMatrix' (wordGate w₂) o t = if t' = t then 1 else 0 := by
    intro t t'
    have h := congrFun (congrFun (wordGate_one_unitary w₂) t') t
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have hK : kraus (((Protocol.nil : Protocol m n 0).condition P hP).word
        (liftData 1 w₁ ++ liftUnread n w₂))
      = fun o => ∑ t : Fin 1 → ZMod 2, LinearMap.toMatrix' (wordGate w₂) o t •
          (LinearMap.toMatrix' (wordGate w₁) * LinearMap.toMatrix' (bornProjection P (t 0))) :=
    funext fun o => kraus_condition_word P hP w₁ w₂ o
  rw [nonselective, hK, krausChannel_sum_smul _ _ hc, Finset.mul_sum, Finset.sum_mul]
  rw [← (Equiv.funUnique (Fin 1) (ZMod 2)).symm.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Equiv.funUnique_symm_apply, uniqueElim_const, Matrix.conjTranspose_mul,
    conjTranspose_bornProjection]
  generalize LinearMap.toMatrix' (wordGate w₁) = U
  generalize LinearMap.toMatrix' (bornProjection P b) = Q
  simp only [Matrix.mul_assoc]

/-! ## The capstones -/

/-- **`ψ ↦ ψ ⊗ |+⟩`**: a normalised `|+⟩` ancilla as a new last bit, `(1/√2)·ψ(init v)`. -/
noncomputable def plusAncilla (N : ℕ) : QubitSpace N →ₗ[ℂ] QubitSpace (N + 1) :=
  invSqrt2 • LinearMap.funLeft ℂ ℂ (fun v : Fin (N + 1) → ZMod 2 => Fin.init v)

/-- **Controlled-H** from bit `c` to bit `t` on `QubitSpace`: the identity on the words where bit
`c` is `0`, and the Hilbert side's `hadamardGate t` on those where it is `1`. -/
noncomputable def controlledHadamardGate (c t : Fin n) : QubitSpace n →ₗ[ℂ] QubitSpace n where
  toFun ψ w := if w c = 0 then ψ w else hadamardGate t ψ w
  map_add' ψ φ := by
    funext w
    by_cases h : w c = 0
    · simp only [Pi.add_apply, if_pos h]
    · simp only [Pi.add_apply, if_neg h, map_add]
  map_smul' a ψ := by
    funext w
    by_cases h : w c = 0
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, if_pos h]
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, if_neg h, map_smul]

/-- **H inject's Kraus family**, on the register's `n` bits, indexed by the outcome string `o` and
the value `d` the measured qubit is read at: a normalised `|+⟩` ancilla (`plusAncilla`); T17's
`kraus` of `hInjectProtocol m j` at `o`; then T15's processing: H on the measured qubit `j`, the
swap of bit `j` and the ancilla (bit `n`), and the measured qubit, now bit `n`, read at `d`. -/
noncomputable def hInjectKraus (m : ℕ) (j : Fin n) (i : (Fin 1 → ZMod 2) × ZMod 2) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  LinearMap.toMatrix' (evalOutcome n (fun _ : Fin 1 => i.2) ∘ₗ
      LinearMap.funLeft ℂ ℂ
        (fun v : Fin (n + 1) → ZMod 2 => v ∘ Equiv.swap j.castSucc (Fin.last n)) ∘ₗ
      hadamardGate j.castSucc) *
    kraus (hInjectProtocol m j) i.1 * LinearMap.toMatrix' (plusAncilla n)

/-- **Remote CH's Kraus family**, on the register's `n` bits, indexed by the outcome string `o`
(`o 0 = s` from `A₁`'s measurement, `o 1 = u` from `B₁`'s) and the string `d` the ebit's halves are
read at (`A₁`, bit `n`, at `d 0`; `B₁`, bit `n + 1`, at `d 1`): two normalised `|+⟩` ancillas;
T17's `kraus` of `remoteCHProtocol k hk c t` at `o`; then T16's processing, the two halves read at
`d`. -/
noncomputable def remoteCHKraus (k : ℕ) (hk : 3 ≤ k) (c t : Fin n)
    (i : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  LinearMap.toMatrix' (evalOutcome n i.2) * kraus (remoteCHProtocol k hk c t) i.1 *
    LinearMap.toMatrix' (plusAncilla (n + 1) ∘ₗ plusAncilla n)

/-! ### Private: the capstones on amplitude functions -/

/-- `(I ⊗ ⟨o|)` reads the function at the word `(y, o)` (`ProtocolSemantics.lean`'s private
`evalOutcome_apply`, restated). -/
private theorem evalOutcome_apply (N : ℕ) {k : ℕ} (o : Fin k → ZMod 2) (ψ : QubitSpace (N + k))
    (y : Fin N → ZMod 2) :
    evalOutcome N o ψ y = ψ (Fin.append y o) :=
  rfl

/-- The Hilbert side's H is the frame's Walsh transform: T18's `runAmp_eq_wordGate` at the
one-letter word. -/
private theorem hadamardGate_eq_walshTransform {N : ℕ} (j : Fin N) (f : QubitSpace N) :
    hadamardGate j f = walshTransform j f := by
  have h := congrFun (runAmp_eq_wordGate (m := 0) [GateLetter.hadamard j]) f
  exact h.symm

/-- Controlled-H on `QubitSpace` is the frame's `controlledHAmp`. -/
private theorem controlledHadamardGate_apply (c t : Fin n) (f : QubitSpace n)
    (w : Fin n → ZMod 2) : controlledHadamardGate c t f w = controlledHAmp c t f w := by
  change (if w c = 0 then f w else hadamardGate t f w)
    = (if w c = 0 then f w else walshTransform t f w)
  rw [hadamardGate_eq_walshTransform]

/-- A family of scalar multiples of one matrix, the scalars' squared moduli summing to one, has
the channel of that matrix. -/
private theorem krausChannel_eq_of_smul {ι α : Type*} [Fintype ι] [Fintype α]
    (K : ι → Matrix α α ℂ) (c : ι → ℂ) (A : Matrix α α ℂ) (hK : ∀ i, K i = c i • A)
    (hc : ∑ i, Complex.normSq (c i) = 1) (ρ : Matrix α α ℂ) :
    krausChannel K ρ = A * ρ * Aᴴ := by
  have h : ∀ i, K i * ρ * (K i)ᴴ = ((Complex.normSq (c i) : ℝ) : ℂ) • (A * ρ * Aᴴ) := by
    intro i
    rw [hK i, Matrix.conjTranspose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
      ← Complex.mul_conj]
    rfl
  rw [krausChannel, Finset.sum_congr rfl fun i _ => h i, ← Finset.sum_smul, ← Complex.ofReal_sum,
    hc, Complex.ofReal_one, one_smul]

/-- The squared modulus of `1/√2` is `½`. -/
private theorem normSq_invSqrt2 : Complex.normSq invSqrt2 = 2⁻¹ := by
  rw [invSqrt2, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (by norm_num)]

/-- Two strings appended on the last two bits are two snocs. -/
private theorem append_two {N : ℕ} (x : Fin N → ZMod 2) (e : Fin 2 → ZMod 2) :
    Fin.append x e = Fin.snoc (Fin.snoc x (e 0)) (e 1) := by
  have he : e = ![e 0, e 1] := by
    funext i
    fin_cases i <;> rfl
  calc Fin.append x e = Fin.append x ![e 0, e 1] := congrArg (Fin.append x) he
    _ = Fin.snoc (Fin.snoc x (e 0)) (e 1) := append_pair x (e 0) (e 1)

section HInjectClosedForm

open FTQCLib.Stabilizer

/-- The branch of outcome `b` read on the register and its ancilla, on amplitude functions
(`HInject.lean`'s private `injectRead`, restated). -/
private noncomputable def injectRead (M : ℕ) (j : Fin n) (f : (Fin n → ZMod 2) → ℂ)
    (b : ZMod 2) : (Fin (n + 1) → ZMod 2) → ℂ :=
  fun u => (hInjectProtocol M j).interpretAmp (fun x => f (Fin.init x))
    (Fin.insertNth (Fin.last (n + 1)) b u)

/-- The correction leaves the outcome bit unchanged (`HInject.lean`'s private
`cnotBitMap_snoc_last`, restated). -/
private theorem cnotBitMap_snoc_last (u : Fin (n + 1) → ZMod 2) (b : ZMod 2) :
    DiagPhase.cnotBitMap (Fin.last (n + 1)) (Fin.last n).castSucc (Fin.snoc u b)
      (Fin.last (n + 1)) = b := by
  unfold DiagPhase.cnotBitMap
  rw [Function.update_of_ne (Fin.castSucc_lt_last _).ne', Fin.snoc_last]

/-- The correction adds the outcome bit to the ancilla (`HInject.lean`'s private
`init_cnotBitMap_snoc`, restated). -/
private theorem init_cnotBitMap_snoc (u : Fin (n + 1) → ZMod 2) (b : ZMod 2) :
    Fin.init (DiagPhase.cnotBitMap (Fin.last (n + 1)) (Fin.last n).castSucc (Fin.snoc u b))
      = Function.update u (Fin.last n) (u (Fin.last n) + b) := by
  unfold DiagPhase.cnotBitMap
  rw [Fin.init_update_castSucc, Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last]

/-- Flipping a bit other than the last commutes with dropping the last (`HInject.lean`'s private
`init_add_single`, restated). -/
private theorem init_add_single (y : Fin (n + 1) → ZMod 2) (j : Fin n) :
    Fin.init (y + Pi.single j.castSucc 1) = Fin.init y + Pi.single j 1 := by
  funext i
  simp only [Fin.init, Pi.add_apply]
  congr 1
  by_cases h : i = j
  · rw [h, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (fun e => h (Fin.castSucc_injective _ e)), Pi.single_eq_of_ne h]

/-- The branch read on the register and its ancilla, in closed form (`HInject.lean`'s private
`injectRead_eq`, restated). -/
private theorem injectRead_eq {M : ℕ} (hm : 1 ≤ M) (j : Fin n) (f : (Fin n → ZMod 2) → ℂ)
    (b : ZMod 2) (u : Fin (n + 1) → ZMod 2) :
    injectRead M j f b u = (1 / 2) *
      ((-1 : ℂ) ^ ((u j.castSucc).val * (u (Fin.last n) + b).val) * f (Fin.init u)
        + (-1 : ℂ) ^ b.val * ((-1 : ℂ) ^ ((u j.castSucc + 1).val * (u (Fin.last n) + b).val)
          * f (Fin.init u + Pi.single j 1))) := by
  have hjL : j.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last j).ne
  unfold injectRead hInjectProtocol
  dsimp only
  rw [Protocol.interpretAmp_word, Protocol.interpretAmp_condition, Protocol.interpretAmp_word,
    Protocol.interpretAmp_nil]
  simp only [runAmp_cons, runAmp_nil, letterAmp, pauliProjection, SignedPauli.act, pauliAct,
    Fin.insertNth_last']
  rw [cnotBitMap_snoc_last, init_cnotBitMap_snoc, yWeight_paulix, zDot_paulix,
    paulix_X, charOf_czGate_eval hm, charOf_czGate_eval hm, init_add_single,
    Fin.init_update_last]
  simp only [Pi.add_apply, Function.update_of_ne hjL, Function.update_self,
    Pi.single_eq_same, Pi.single_eq_of_ne hjL.symm, add_zero, ZMod.val_zero, pow_zero, one_mul]

/-- Flipping a bit set to `x` sets it to `x + 1` (`HInject.lean`'s private `update_add_single`,
restated). -/
private theorem update_add_single (w : Fin n → ZMod 2) (j : Fin n) (x : ZMod 2) :
    Function.update w j x + Pi.single j 1 = Function.update w j (x + 1) := by
  funext i
  by_cases h : i = j
  · subst h
    rw [Pi.add_apply, Function.update_self, Function.update_self, Pi.single_eq_same]
  · rw [Pi.add_apply, Function.update_of_ne h, Function.update_of_ne h, Pi.single_eq_of_ne h,
      add_zero]

/-- The four values of the Walsh combination of the closed form (`HInject.lean`'s private
`walsh_combination`, restated). -/
private theorem walsh_combination (c a b : ZMod 2) (F0 F1 : ℂ) :
    (1 / (Real.sqrt 2 : ℂ)) *
      ((1 / 2) * ((-1 : ℂ) ^ ((0 : ZMod 2).val * (a + b).val) * F0
          + (-1 : ℂ) ^ b.val * ((-1 : ℂ) ^ ((1 : ZMod 2).val * (a + b).val) * F1))
        + signOf c * ((1 / 2) * ((-1 : ℂ) ^ ((1 : ZMod 2).val * (a + b).val) * F1
          + (-1 : ℂ) ^ b.val * ((-1 : ℂ) ^ ((0 : ZMod 2).val * (a + b).val) * F0))))
      = if c = b then (1 / (Real.sqrt 2 : ℂ)) * (F0 + signOf a * F1) else 0 := by
  rcases zmod_two_eq_zero_or_one c with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp (config := { decide := true }) [signOf] <;> ring

/-- H on the measured qubit of the closed form (`HInject.lean`'s private `walsh_injectRead`,
restated). -/
private theorem walsh_injectRead {M : ℕ} (hm : 1 ≤ M) (j : Fin n) (f : (Fin n → ZMod 2) → ℂ)
    (b : ZMod 2) (v : Fin (n + 1) → ZMod 2) :
    walshTransform j.castSucc (injectRead M j f b) v
      = if v j.castSucc = b then (1 / (Real.sqrt 2 : ℂ)) *
          (f (Function.update (Fin.init v) j 0)
            + signOf (v (Fin.last n)) * f (Function.update (Fin.init v) j 1))
        else 0 := by
  have hjL : j.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last j).ne
  unfold walshTransform
  rw [injectRead_eq hm, injectRead_eq hm]
  simp only [Function.update_self, Function.update_of_ne hjL.symm, Fin.init_update_castSucc,
    update_add_single]
  rw [zero_add, show (1 + 1 : ZMod 2) = 0 from rfl]
  exact walsh_combination (v j.castSucc) (v (Fin.last n)) b _ _

/-- With the ancilla moved into the input qubit's place and the measured qubit read at `d`, the
closed form is the Walsh transform of the register at the input qubit where `d` is the outcome
`b`, and zero elsewhere (`HInject.lean`'s private `walsh_injectRead_swap`, restated and extended
to `d ≠ b`). -/
private theorem walsh_injectRead_swap {M : ℕ} (hm : 1 ≤ M) (j : Fin n)
    (f : (Fin n → ZMod 2) → ℂ) (b d : ZMod 2) (w : Fin n → ZMod 2) :
    walshTransform j.castSucc (injectRead M j f b)
        (Fin.insertNth (Fin.last n) d w ∘ Equiv.swap j.castSucc (Fin.last n))
      = if d = b then walshTransform j f w else 0 := by
  have h1 : (Fin.insertNth (Fin.last n) d w ∘ Equiv.swap j.castSucc (Fin.last n)) j.castSucc
      = d := by
    rw [Function.comp_apply, Equiv.swap_apply_left, Fin.insertNth_last', Fin.snoc_last]
  have h2 : (Fin.insertNth (Fin.last n) d w ∘ Equiv.swap j.castSucc (Fin.last n)) (Fin.last n)
      = w j := by
    rw [Function.comp_apply, Equiv.swap_apply_right, Fin.insertNth_last', Fin.snoc_castSucc]
  have h3 : Fin.init (Fin.insertNth (Fin.last n) d w ∘ Equiv.swap j.castSucc (Fin.last n))
      = Function.update w j d := by
    funext i
    rw [Fin.init, Function.comp_apply]
    by_cases h : i = j
    · subst h
      rw [Equiv.swap_apply_left, Fin.insertNth_last', Fin.snoc_last, Function.update_self]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun e => h (Fin.castSucc_injective _ e))
        (Fin.castSucc_lt_last i).ne, Fin.insertNth_last', Fin.snoc_castSucc,
        Function.update_of_ne h]
  rw [walsh_injectRead hm, h1]
  by_cases hd : d = b
  · rw [if_pos hd, if_pos hd, h2, h3, Function.update_idem, Function.update_idem]
    rfl
  · rw [if_neg hd, if_neg hd]

end HInjectClosedForm

/-- **H inject's composite on one input**: the ancilla, the protocol's `K_o`, H on the measured
qubit, the swap, and the measured qubit read at `d` give `1/√2` times H on the input where
`d = o 0`, and zero elsewhere. -/
private theorem hInject_apply (hm : 1 ≤ m) (j : Fin n) (o : Fin 1 → ZMod 2) (d : ZMod 2)
    (ψ : QubitSpace n) (w : Fin n → ZMod 2) :
    hadamardGate j.castSucc
        (fun y => hilbertSem (hInjectProtocol m j) (plusAncilla n ψ) (Fin.append y o))
        (Fin.append w (fun _ : Fin 1 => d) ∘ Equiv.swap j.castSucc (Fin.last n))
      = (if d = o 0 then invSqrt2 else 0) * hadamardGate j ψ w := by
  have hin : (fun y => hilbertSem (hInjectProtocol m j) (plusAncilla n ψ) (Fin.append y o))
      = invSqrt2 • injectRead m j ψ (o 0) := by
    funext y
    rw [plusAncilla, LinearMap.smul_apply, map_smul, Pi.smul_apply, Pi.smul_apply,
      ← interpretAmp_eq_hilbertSem, Fin.append_right_eq_snoc, ← Fin.insertNth_last']
    rfl
  rw [hin, map_smul, Pi.smul_apply, smul_eq_mul, hadamardGate_eq_walshTransform,
    hadamardGate_eq_walshTransform, Fin.append_right_eq_snoc, ← Fin.insertNth_last',
    walsh_injectRead_swap hm]
  by_cases hd : d = o 0
  · rw [if_pos hd, if_pos hd]
  · rw [if_neg hd, if_neg hd, mul_zero, zero_mul]

/-- **H inject's Kraus operator** at `(o, d)` is `1/√2` times `H_j` where `d = o 0`, and zero
elsewhere. -/
private theorem hInjectKraus_eq (hm : 1 ≤ m) (j : Fin n) (i : (Fin 1 → ZMod 2) × ZMod 2) :
    hInjectKraus m j i
      = (if i.2 = i.1 0 then invSqrt2 else 0) • LinearMap.toMatrix' (hadamardGate j) := by
  rw [hInjectKraus, kraus, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp,
    ← LinearEquiv.map_smul]
  refine congrArg LinearMap.toMatrix' (LinearMap.ext fun ψ => funext fun w => ?_)
  rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, ← hInject_apply hm j i.1 i.2 ψ w]
  rfl

/-- H inject's scalars: `1/√2` at the two pairs with `d = o 0`, so their squared moduli sum to
one. -/
private theorem hInject_scalars :
    ∑ i : (Fin 1 → ZMod 2) × ZMod 2, Complex.normSq (if i.2 = i.1 0 then invSqrt2 else 0) = 1 := by
  rw [Fintype.sum_prod_type]
  have h : ∀ o : Fin 1 → ZMod 2,
      ∑ d : ZMod 2, Complex.normSq (if d = o 0 then invSqrt2 else 0) = 2⁻¹ := by
    intro o
    simp only [apply_ite Complex.normSq, map_zero]
    rw [Finset.sum_ite_eq' Finset.univ (o 0), if_pos (Finset.mem_univ _), normSq_invSqrt2]
  rw [Finset.sum_congr rfl fun o _ => h o, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    ZMod.card, Fintype.card_fin, nsmul_eq_mul]
  norm_num

section RemoteCHClosedForm

open FTQCLib.Stabilizer

/-- **The referee off the measured bits** is zero (`RemoteCH.lean`'s private
`interpretAmp_remoteCHProtocol_of_ne`, restated). -/
private theorem interpretAmp_remoteCHProtocol_of_ne (k : ℕ) (hk : 3 ≤ k) (c t : Fin n)
    (f : (Fin n → ZMod 2) → ℂ) (w : Fin n → ZMod 2) {a b s u : ZMod 2} (h : a ≠ s ∨ b ≠ u) :
    (remoteCHProtocol k hk c t).interpretAmp (fun x => f (Fin.init (Fin.init x)))
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc w a) b) s) u) = 0 := by
  unfold remoteCHProtocol
  dsimp only
  rw [Protocol.interpretAmp_word, Protocol.interpretAmp_condition, Protocol.interpretAmp_word,
    Protocol.interpretAmp_condition, Protocol.interpretAmp_word, Protocol.interpretAmp_nil]
  simp only [runAmp_append, runAmp_cons, runAmp_nil, runAmp_controlledHWord]
  simp only [letterAmp, pauliProjection_signedZ, walshTransform, controlledHAmp,
    DiagPhase.cnotBitMap, Fin.snoc_last, Fin.snoc_castSucc, Fin.init_snoc, ← Fin.snoc_update,
    Fin.update_snoc_last, charOf_czGate_eval (by omega : 1 ≤ k)]
  rcases h with h | h
  · simp only [if_neg h, mul_zero, add_zero, ite_self]
  · simp only [if_neg h, mul_zero]

end RemoteCHClosedForm

/-- **Remote CH's composite on one input**: the two ancillas, the protocol's `K_o`, and the ebit's
halves read at `d` give `½` times controlled-H where `d = o`, and zero elsewhere. -/
private theorem remoteCH_apply (k : ℕ) (hk : 3 ≤ k) {c t : Fin n} (hct : c ≠ t)
    (o d : Fin 2 → ZMod 2) (ψ : QubitSpace n) (w : Fin n → ZMod 2) :
    hilbertSem (remoteCHProtocol k hk c t) ((plusAncilla (n + 1) ∘ₗ plusAncilla n) ψ)
        (Fin.append (Fin.append w d) o)
      = (if d = o then (2⁻¹ : ℂ) else 0) * controlledHadamardGate c t ψ w := by
  have hin : (plusAncilla (n + 1) ∘ₗ plusAncilla n) ψ
      = (2⁻¹ : ℂ) • fun x : Fin (n + 2) → ZMod 2 => ψ (Fin.init (Fin.init x)) := by
    rw [LinearMap.comp_apply, plusAncilla, plusAncilla, LinearMap.smul_apply, LinearMap.smul_apply,
      map_smul, smul_smul, invSqrt2_mul_self]
    rfl
  rw [hin, map_smul, Pi.smul_apply, smul_eq_mul, ← interpretAmp_eq_hilbertSem, append_two w d,
    append_two _ o, controlledHadamardGate_apply]
  by_cases h : d = o
  · subst h
    rw [if_pos rfl, interpretAmp_remoteCHProtocol k hk hct]
  · rw [if_neg h, zero_mul, interpretAmp_remoteCHProtocol_of_ne k hk c t _ _ ?_, mul_zero]
    by_contra hne
    push Not at hne
    exact h (funext fun x => by fin_cases x; exacts [hne.1, hne.2])

/-- **Remote CH's Kraus operator** at `(o, d)` is `½` times controlled-H where `d = o`, and zero
elsewhere. -/
private theorem remoteCHKraus_eq (k : ℕ) (hk : 3 ≤ k) {c t : Fin n} (hct : c ≠ t)
    (i : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :
    remoteCHKraus k hk c t i
      = (if i.2 = i.1 then (2⁻¹ : ℂ) else 0) • LinearMap.toMatrix' (controlledHadamardGate c t) := by
  rw [remoteCHKraus, kraus, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp,
    ← LinearEquiv.map_smul]
  refine congrArg LinearMap.toMatrix' (LinearMap.ext fun ψ => funext fun w => ?_)
  rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, ← remoteCH_apply k hk hct i.1 i.2 ψ w,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, evalOutcome_apply,
    evalOutcome_apply]

/-- Remote CH's scalars: `½` at the four pairs with `d = o`, so their squared moduli sum to one. -/
private theorem remoteCH_scalars :
    ∑ i : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2),
      Complex.normSq (if i.2 = i.1 then (2⁻¹ : ℂ) else 0) = 1 := by
  rw [Fintype.sum_prod_type]
  have h : ∀ o : Fin 2 → ZMod 2,
      ∑ d : Fin 2 → ZMod 2, Complex.normSq (if d = o then (2⁻¹ : ℂ) else 0) = 4⁻¹ := by
    intro o
    simp only [apply_ite Complex.normSq, map_zero]
    rw [Finset.sum_ite_eq' Finset.univ o, if_pos (Finset.mem_univ _), map_inv₀,
      Complex.normSq_ofNat]
    norm_num
  rw [Finset.sum_congr rfl fun o _ => h o, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    ZMod.card, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **H inject in Hilbert space.** At any precision `m ≥ 1` and any input qubit `j`, every Kraus
operator of H inject is a scalar multiple of `G = H_j`, the scalar `1/√2` where the measured qubit
is read at the outcome and `0` elsewhere; the scalars' squared moduli sum to one; so the channel is
`ρ ↦ G ρ G†`. T15's `hInject_correct` carried across T17 to T20. Proved at T21.3.2. -/
theorem hInject_channel_eq (hm : 1 ≤ m) (j : Fin n) :
    (∀ i, hInjectKraus m j i
        = (if i.2 = i.1 0 then invSqrt2 else 0) • LinearMap.toMatrix' (hadamardGate j)) ∧
      ∑ i : (Fin 1 → ZMod 2) × ZMod 2, Complex.normSq (if i.2 = i.1 0 then invSqrt2 else 0) = 1 ∧
      ∀ ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ,
        krausChannel (hInjectKraus m j) ρ
          = LinearMap.toMatrix' (hadamardGate j) * ρ * (LinearMap.toMatrix' (hadamardGate j))ᴴ :=
  ⟨hInjectKraus_eq hm j, hInject_scalars,
    krausChannel_eq_of_smul _ _ _ (hInjectKraus_eq hm j) hInject_scalars⟩

/-- **Remote CH in Hilbert space.** At any precision `k ≥ 3` and any two distinct bits `c ≠ t` of
the register, every Kraus operator of remote CH is a scalar multiple of `G`, controlled-H from `c`
to `t`, the scalar `1/2` where the ebit's halves are read at the outcome string and `0` elsewhere;
the scalars' squared moduli sum to one; so the channel is `ρ ↦ G ρ G†`. T16's `remoteCH_correct`
carried across T17 to T20. Proved at T21.3.2. -/
theorem remoteCH_channel_eq (k : ℕ) (hk : 3 ≤ k) {c t : Fin n} (hct : c ≠ t) :
    (∀ i, remoteCHKraus k hk c t i
        = (if i.2 = i.1 then (2⁻¹ : ℂ) else 0) • LinearMap.toMatrix' (controlledHadamardGate c t)) ∧
      ∑ i : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2),
          Complex.normSq (if i.2 = i.1 then (2⁻¹ : ℂ) else 0) = 1 ∧
      ∀ ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ,
        krausChannel (remoteCHKraus k hk c t) ρ
          = LinearMap.toMatrix' (controlledHadamardGate c t) * ρ *
              (LinearMap.toMatrix' (controlledHadamardGate c t))ᴴ :=
  ⟨remoteCHKraus_eq k hk hct, remoteCH_scalars,
    krausChannel_eq_of_smul _ _ _ (remoteCHKraus_eq k hk hct) remoteCH_scalars⟩

end FTQCLib.Hilbert

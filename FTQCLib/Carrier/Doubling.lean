/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.FrameCategory
import FTQCLib.Carrier.UnreadBits

/-!
# The doubling: a protocol's Choi state, its channel, and the tower's ring condition

The statement of T49 (`docs/TARGETS.md`; `docs/fidelity/T49.md`; `docs/decisions/T49.md`). A channel
is a state with its data bits doubled, its read and unread outcome bits attached.

**The Choi state** (`choi`). For a protocol `p : Protocol m n k` (T14) the Choi state is T14's
interpretation of `p` on the Bell floor of `n` pairs, with `p`'s letters acting on the second half.
The Bell floor is T46's identity `idState n` (`δ_{x = y}` at scale `1` and height `0`, a carrier
state by `isCarrier_idState`), lifted by R7 to `p`'s precision: `idAt n m`, which is
`liftPrecision (idState n) (max 1 m) _`, T46's own floor at a precision, so no second copy is
defined here. The letters are moved onto the second half by `Protocol.onSecondHalf`: data bit `i`
of `p`'s register goes to `n + i`, outcome bit `j` to `n + n + j` (`secondHalfBit`), letter by
letter and Pauli by Pauli; the first `n` bits are spectators. Nothing is defined on operators: the
Choi state is a carrier state built by T14's interpretation, its register `(r, w, o)` the
reference bits, the data bits and the outcome bits, and by linearity of the referee its amplitude
is `(r, w, o) ↦ (interpretAmp p δ_r)(w, o)`. The map-state duality is the source's (Backens, cited
below); the Bell-floor form, the unnormalised identity and the letters on the second half are the
frame's own.

**Read and unread outcome bits.** Which outcome bits are read is a choice made when the channel is
read, not part of the protocol: a **reading** is an equivalence `σ : Fin k ≃ Fin (r + u)`, outcome
bit `j` read when `σ j < r` and unread otherwise. T27's `UnreadEq` takes the unread bits last, so
`choiRead p σ` reindexes the Choi state's outcome bits by `σ` (`readingEquiv`, through T46's
`reindexFreeBits`): the reference, data and read outcome bits first, kept as outputs, and the `u`
unread bits last.

**Stinespring, D2's form.** The dilation is the referee: `dilation p σ` is the matrix of
`interpretAmp p` on point masses, its rows the data bits with the read outcome bits and, apart, the
unread ones. It is an isometry, `innerSum_interpretAmp` (proved here: each word keeps inner sums,
`innerSum_runAmp`, and each conditioning letter `Σ_b ∣b⟩ ⊗ Π_b` is an isometry, the projections
being orthogonal halves). The channel `channel p σ` is `ρ ↦ Tr_unread (V ρ Vᴴ)` with
`V = dilation p σ`: D2's deferred measurement, every outcome a free bit, traced out when unread
and kept coherently when read.

**Channel equality** (`choi_eq_iff`, the coherent reading). Two protocols on the same data bits,
read with the same numbers of read and unread outcome bits, have Choi states equal up to their
unread bits (T27's `UnreadEq`, the unread bits last and the read bits kept) exactly when their
channels are equal. The Gram data of `choiRead p σ` at `((x, y, o), (x′, y′, o′))` is the channel's
matrix entry at `(y, o), (y′, o′)` on the input `∣x⟩⟨x′∣`, so this is the Choi–Jamiołkowski
correspondence for the channel, on T27's relation.

**The measured reading** (`choi_measured_eq_iff`). The coherent reading is not equality branch by
branch: conditioning on `Z` with the outcome read, against the same followed by `Z` on the
outcome bit, has equal branches up to sign and Choi states that are not `UnreadEq` (T49.2's rows
`P1`, `P2`). For the measured reading each read outcome bit is copied into a fresh unread bit
(`measured`): one conditioning letter on `Z` of that bit, which creates a new outcome bit equal to it
(`pauliProjection_zPauli_single`), read as unread (`measuredReading`). Then equality up to unread
bits holds exactly when, at every read outcome string `o` and on every input `f`, the branches
(`readBranch`: the read outcome bits evaluated at `o`, the unread ones kept as the last bits) have
the same Gram data. The inputs are every amplitude function, through the referee, not only the
carrier states at the protocol's precision: at precision `1` real inputs fix only the symmetric
part of a branch's channel (fidelity note, Claim 5).

**The tower** (`choi_mem_dyadic`). A protocol's Choi amplitude takes its values in
`ℤ[ζ_{2^∞}, ½]` (`dyadicCyclotomicRing`, T27): every letter's matrix has its entries there (`1/√2`
and signs for H, roots of unity of order a power of two for a diagonal letter, a permutation for
CNOT, `½`, signs and `i` for a projection), and so does the floor. That is a necessary condition for
a channel to be in the tower; a channel none of whose dilations has such amplitudes, up to one
unit-modulus scalar, is outside it. The tower is stated by this ring condition and never by
carrier-ness of the Choi state: the rotation with cosine `3/5` has a Choi amplitude that is a
carrier state's at precision `1`, and no protocol realises it, since `1/5` is outside the ring
(`intCast_div_five_not_mem_dyadicCyclotomicRing`; T49.2's inhabitation row). The converse of the
ring condition is T45's exact synthesis, open here and not stated.

## Main definitions

* `secondHalfBit`, `secondHalfLetter`, `secondHalfPauli`, `Protocol.onSecondHalf` — a protocol on
  `n` data bits moved onto the second half of the doubled register.
* `choi` — the Choi state, T14's interpretation on the Bell floor `idAt n m`.
* `readingEquiv`, `choiRead` — the Choi state with its outcome bits reordered by a reading, the
  unread bits last.
* `dilation`, `channel` — the Stinespring isometry (the referee) and its trace over the unread bits.
* `copyReadBits`, `measured`, `measuredReading`, `readBranch` — the measured reading and the
  branches at a read outcome string.

## Main results

* `innerSum_interpretAmp`, `interpretAmp_add_smul` — the referee of a protocol is a linear isometry
  (proved here).
* `isCarrier_choi`, `amp_choi` — the Choi state is a carrier state at `p`'s precision, with the
  Choi amplitude `(x, v) ↦ interpretAmp p δ_x v` (T49.3.1).
* `choi_gram_eq_iff` — Choi states with equal Gram data, at any numbers of unread bits, exactly
  when the channels are equal (T49.3.1).
* `choi_eq_iff` — Choi states equal up to unread bits exactly when the channels are equal (T49.3).
* `choi_measured_eq_iff` — for the measured reading, exactly when the branches agree on every input
  up to unread bits (T49.3).
* `choi_mem_dyadic` — a protocol's Choi amplitude lies in `dyadicCyclotomicRing` (T49.3).
* `isDilation_dilation`, `channel_ne_of_forall_dilation` — the dilation is one of the channel's, so
  a map none of whose dilations has values in the ring, up to a unit-modulus scalar, is no
  protocol's channel (T49.3.2).
* `rotation_not_realised` — the rotation with cosine `3/5` is no protocol's channel (T49.3.2).

## Implementation notes

* **Precision.** The theorems take `1 ≤ m`: `amp_interpret` needs the floor at the protocol's own
  precision, `max 1 m = m`, and a protocol at precision `0` runs on no carrier state (`IsCarrier`
  needs `1 ≤ S.m`). The definitions are total, through `max 1 m`.
* **Equal counts.** `choi_eq_iff` compares readings with the same `r` and `u`, as `UnreadEq` is on
  one register. Readings with different numbers of unread bits are compared by their Gram data
  (`choi_gram_eq_iff`): `gram` sums over the unread bits, so the Gram data over `u` and over `u'`
  unread bits are functions of the same read words, and no padding is needed (docs/STEPS.md, entry
  2026-10-02i).
* **Indices.** The channel's input index is `Fin n → ZMod 2` and its output index the pair (data
  bits, read outcome bits); the dilation's rows add the unread bits as a second component. The
  Choi state's read words are words of `Fin ((n + n) + r)`; relating the two is the proof's.

## References

* M. Backens, *The ZX-calculus is complete for stabilizer quantum mechanics*, arXiv:1307.7025:
  map-state duality, operators from `n` to `m` qubits against states on `n + m` qubits; cited above
  `choi`. Its statement is for operators; the channel form, on Gram data with unread bits, is the
  frame's own (fidelity note).
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Matrix

/-! ## The second half of the doubled register -/

/-- A bit of a protocol's register, `n` data bits then `k` outcome bits, read on the doubled
register of `(n + n) + k` bits: data bit `i` at `n + i`, outcome bit `j` at `n + n + j`. -/
def secondHalfBit (n k : ℕ) (i : Fin (n + k)) : Fin ((n + n) + k) :=
  Fin.cast (Nat.add_assoc n n k).symm (Fin.natAdd n i)

/-- A letter on `n + k` bits, moved onto the doubled register by `secondHalfBit`: H and CNOT at the
moved bits, a diagonal exponent with its variables renamed. -/
noncomputable def secondHalfLetter (n : ℕ) {k M : ℕ} :
    GateLetter (n + k) M → GateLetter ((n + n) + k) M
  | .hadamard i => .hadamard (secondHalfBit n k i)
  | .diagonal D => .diagonal (MvPolynomial.rename (secondHalfBit n k) D)
  | .cnot i j hij => .cnot (secondHalfBit n k i) (secondHalfBit n k j)
      fun h => hij ((Fin.natAdd_inj n).mp (Fin.cast_injective _ h))

/-- A Pauli with its sign on `n + k` qubits, moved onto the doubled register: identity on the first
`n` qubits, the Pauli on the rest. -/
def secondHalfPauli (n : ℕ) {k : ℕ} (P : SignedPauli (n + k)) : SignedPauli ((n + n) + k) :=
  ⟨P.sign, ⟨Fin.append 0 P.pauli.X ∘ Fin.cast (Nat.add_assoc n n k),
    Fin.append 0 P.pauli.Z ∘ Fin.cast (Nat.add_assoc n n k)⟩⟩

/-- Moving a Pauli onto the second half keeps its number of Y: the first `n` qubits carry none. -/
theorem yWeight_secondHalfPauli (n : ℕ) {k : ℕ} (P : SignedPauli (n + k)) :
    yWeight (secondHalfPauli n P).pauli = yWeight P.pauli := by
  unfold yWeight zDot secondHalfPauli
  calc _ = ∑ j : Fin (n + (n + k)), (Fin.append (0 : Fin n → ZMod 2) P.pauli.Z j).val
          * (Fin.append (0 : Fin n → ZMod 2) P.pauli.X j).val :=
        Fintype.sum_equiv (finCongr (Nat.add_assoc n n k)) _ _ (fun _ => rfl)
    _ = _ := by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, ZMod.val_zero, zero_mul,
          Finset.sum_const_zero, zero_add]

namespace Protocol

variable {m n : ℕ}

/-- **A protocol on the second half.** `p`'s letters moved onto the doubled register of `n + n`
data bits, the first `n` spectators: each word letter by letter (`secondHalfLetter`), each
conditioning letter's Pauli by `secondHalfPauli`, which keeps the number of Y and so the
precision condition. -/
noncomputable def onSecondHalf : {k : ℕ} → Protocol m n k → Protocol m (n + n) k
  | _, nil => nil
  | _, word p w => word (onSecondHalf p) (w.map (secondHalfLetter n))
  | _, condition p P hP => condition (onSecondHalf p) (secondHalfPauli n P)
      (by rw [yWeight_secondHalfPauli]; exact hP)

end Protocol

/-! ## The Choi state -/

-- source: papers/categorical_qm/
-- Backens_2014_zx_calculus_complete_stabilizer_1307.7025 theorem:thm:Choi-Jamiolkowski
/-- **The Choi state** of a protocol: T14's interpretation of `p` on the Bell floor of `n` pairs,
T46's identity lifted by R7 to `p`'s precision (`idAt n m`), with `p`'s letters on the second half
(`Protocol.onSecondHalf`). Its register is the `n` reference bits, the `n` data bits and the `k`
outcome bits. The source's map-state duality is for operators and the normalised cup; here the
floor is `δ_{x = y}` at scale `1` (T46's identity, not the normalised Bell state) and the operator
is a protocol's referee, read through T14's interpretation, so nothing is defined on operators. -/
noncomputable def choi {m n k : ℕ} (p : Protocol m n k) : KernelSumState ((n + n) + k) :=
  p.onSecondHalf.interpret (idAt n m)

/-! ## Readings: read outcome bits kept, unread ones last -/

/-- **The register reordered by a reading** `σ : Fin k ≃ Fin (r + u)` of the `k` outcome bits after
`N` bits: the first `N` bits fixed, outcome bit `j` sent to position `N + σ j`, so the `r` read
outcome bits follow the first `N` and the `u` unread ones come last. -/
def readingEquiv (N : ℕ) {k r u : ℕ} (σ : Fin k ≃ Fin (r + u)) : Fin (N + k) ≃ Fin ((N + r) + u) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin N)) σ).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_assoc N r u).symm)))

/-- **The Choi state read through `σ`**: `choi p` with its outcome bits reordered by
`readingEquiv`, the reference, data and read outcome bits first and the `u` unread bits last, the
form T27's `UnreadEq u` reads. Its amplitude at a word `v` is `amp (choi p) (v ∘ readingEquiv _ σ)`
(`amp_reindexFreeBits`). -/
noncomputable def choiRead {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u)) :
    KernelSumState (((n + n) + r) + u) :=
  reindexFreeBits (Fin.equiv_iff_eq.mp ⟨readingEquiv (n + n) σ⟩) (readingEquiv (n + n) σ) (choi p)

/-! ## Stinespring: the dilation and the channel -/

/-- **The dilation** of a protocol read through `σ` (Stinespring, in D2's form): the matrix of the
referee `interpretAmp p` on point masses. Its column is the input word `x`; its row is the output
word, the data bits with the read outcome bits, and apart the unread outcome bits, outcome bit `j`
taking the value at position `σ j` of the read and unread outcome words appended. -/
noncomputable def dilation {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u)) :
    Matrix (((Fin n → ZMod 2) × (Fin r → ZMod 2)) × (Fin u → ZMod 2)) (Fin n → ZMod 2) ℂ :=
  fun a x => p.interpretAmp (delta x) (Fin.append a.1.1 (Fin.append a.1.2 a.2 ∘ σ))

/-- **The channel** of a protocol read through `σ`: `ρ ↦ Tr_unread (V ρ Vᴴ)` with `V` the dilation,
the unread outcome bits traced out and the read ones kept, coherently, beside the data bits. -/
noncomputable def channel {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    Matrix ((Fin n → ZMod 2) × (Fin r → ZMod 2)) ((Fin n → ZMod 2) × (Fin r → ZMod 2)) ℂ :=
  fun a b => ∑ e : Fin u → ZMod 2, (dilation p σ * ρ * (dilation p σ)ᴴ) (a, e) (b, e)

/-- **A dilation of a map on matrices** (Stinespring's form): `Φ ρ` is `D ρ Dᴴ` traced over the
environment `ε`, at every `ρ`. No isometry condition: a dilation here is any Kraus family read as
one matrix, as the tower clause needs (docs/STEPS.md, entry 2026-10-02i). -/
def IsDilation {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
    (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ) (D : Matrix (κ × ε) ι ℂ) : Prop :=
  ∀ ρ, Φ ρ = fun a b => ∑ e : ε, (D * ρ * Dᴴ) (a, e) (b, e)

/-- **The rotation with cosine `3/5`** on one bit, row the output and column the input:
`[[3/5, −4/5], [4/5, 3/5]]`. Its Choi amplitude is a carrier state's at precision `1` (T49.2's
inhabitation row), and it is no protocol's channel (`rotation_not_realised`). -/
noncomputable def rotationThreeFifths : Matrix (Fin 1 → ZMod 2) (Fin 1 → ZMod 2) ℂ :=
  fun y x => if y = x then 3 / 5 else if x 0 = 0 then 4 / 5 else -(4 / 5)

/-! ### The referee is a linear isometry -/

/-- The projection `Π_b` is linear in the function it projects. -/
private theorem pauliProjection_add_smul {N : ℕ} (P : SignedPauli N) (b : ZMod 2)
    (f g : (Fin N → ZMod 2) → ℂ) (c : ℂ) :
    pauliProjection P b (f + c • g) = pauliProjection P b f + c • pauliProjection P b g := by
  funext w
  simp only [pauliProjection_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The referee of a protocol is linear**, letter by letter (`runAmp_add_smul`, and the
projection's linearity). -/
theorem interpretAmp_add_smul {m n k : ℕ} (p : Protocol m n k) (f g : (Fin n → ZMod 2) → ℂ)
    (c : ℂ) : p.interpretAmp (f + c • g) = p.interpretAmp f + c • p.interpretAmp g := by
  induction p with
  | nil => rfl
  | word p w ih => rw [Protocol.interpretAmp_word, Protocol.interpretAmp_word,
      Protocol.interpretAmp_word, ih, runAmp_add_smul]
  | condition p P hP ih =>
    funext v
    simp only [Protocol.interpretAmp_condition, ih, pauliProjection_add_smul, Pi.add_apply,
      Pi.smul_apply]

/-- Polarization: a linear map keeping `⟨f, f⟩` keeps every inner sum, from the expansions at
`a + b` and `a + i b`. -/
private theorem innerSum_map_eq {α β : Type*} [Fintype α] [Fintype β] (T : (α → ℂ) → (β → ℂ))
    (hlin : ∀ (a b : α → ℂ) (c : ℂ), T (a + c • b) = T a + c • T b)
    (hnorm : ∀ f, innerSum (T f) (T f) = innerSum f f) (a b : α → ℂ) :
    innerSum (T a) (T b) = innerSum a b := by
  have hone := hnorm (a + (1 : ℂ) • b)
  have hI := hnorm (a + Complex.I • b)
  rw [hlin, innerSum_add_smul_self, innerSum_add_smul_self, hnorm a, hnorm b] at hone hI
  rw [map_one] at hone
  rw [Complex.conj_I] at hI
  linear_combination (1 / 2 : ℂ) * hone + (Complex.I / 2) * hI
    + ((innerSum (T a) (T b) - innerSum a b - (innerSum (T b) (T a) - innerSum b a)) / 2)
      * Complex.I_sq

/-- A conditioning letter `Σ_b ∣b⟩ ⊗ Π_b` keeps inner sums: it is linear and keeps `Σ |·|²`
(`sum_normSq_projection`). -/
private theorem innerSum_projection {N : ℕ} (P : SignedPauli N) (a b : (Fin N → ZMod 2) → ℂ) :
    innerSum (fun v : Fin (N + 1) → ZMod 2 => pauliProjection P (v (Fin.last N)) a (Fin.init v))
      (fun v : Fin (N + 1) → ZMod 2 => pauliProjection P (v (Fin.last N)) b (Fin.init v))
      = innerSum a b := by
  refine innerSum_map_eq
    (fun f (v : Fin (N + 1) → ZMod 2) => pauliProjection P (v (Fin.last N)) f (Fin.init v))
    (fun f g c => ?_) (fun f => ?_) a b
  · funext v
    simp only [pauliProjection_add_smul, Pi.add_apply, Pi.smul_apply]
  · rw [innerSum_self, innerSum_self]
    exact congrArg _ (sum_normSq_projection P f)

/-- **Stinespring, D2's form: the referee of a protocol is an isometry.** It keeps every inner sum
`Σ a · conj b`: each word does (`innerSum_runAmp`) and each conditioning letter does
(`Σ_b ∣b⟩ ⊗ Π_b` with `Π_0 + Π_1 = 1` orthogonal projections). So `dilation p σ` is an isometry
and `channel p σ` is its trace over the unread bits. -/
theorem innerSum_interpretAmp {m n k : ℕ} (p : Protocol m n k) (a b : (Fin n → ZMod 2) → ℂ) :
    innerSum (p.interpretAmp a) (p.interpretAmp b) = innerSum a b := by
  induction p with
  | nil => rfl
  | word p w ih => rw [Protocol.interpretAmp_word, Protocol.interpretAmp_word, innerSum_runAmp, ih]
  | condition p P hP ih =>
    rw [Protocol.interpretAmp_condition, Protocol.interpretAmp_condition, innerSum_projection, ih]

/-! ## The measured reading -/

/-- A `Z` Pauli has no Y. -/
private theorem yWeight_zPauli {N : ℕ} (v : Fin N → ZMod 2) : yWeight (zPauli v) = 0 := by
  unfold yWeight zDot zPauli
  simp

/-- Conditioning on a `Z` Pauli keeps any precision: it has no Y. -/
theorem zPauli_precision {N : ℕ} (m : ℕ) (v : Fin N → ZMod 2) :
    yWeight (⟨0, zPauli v⟩ : SignedPauli N).pauli % 2 = 1 → 2 ≤ m := by
  intro h
  rw [yWeight_zPauli] at h
  exact absurd h (by decide)

/-- **The first `t` read outcome bits copied.** After `p`, for each read position `s < t` of the
reading `σ`, one conditioning letter on `Z` of the outcome bit `σ⁻¹ s`: it creates a new outcome
bit equal to that bit (`pauliProjection_zPauli_single`), the copy, as outcome `k + s`. -/
noncomputable def copyReadBits {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u)) :
    (t : ℕ) → t ≤ r → Protocol m n (k + t)
  | 0, _ => p
  | t + 1, ht => (copyReadBits p σ t (Nat.le_of_succ_le ht)).condition
      ⟨0, zPauli (Pi.single (Fin.natAdd n (Fin.castAdd t (σ.symm (Fin.castAdd u ⟨t, ht⟩)))) 1)⟩
      (zPauli_precision m _)

/-- **The measured protocol**: `p` with each of its `r` read outcome bits copied into a fresh
outcome bit. -/
noncomputable def measured {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u)) :
    Protocol m n (k + r) :=
  copyReadBits p σ r le_rfl

/-- **The measured reading** of the `k + r` outcome bits of `measured p σ`: the read outcome bits
read as `σ` reads them, and both the unread outcome bits and the `r` copies unread, the copies
last. -/
def measuredReading {k r u : ℕ} (σ : Fin k ≃ Fin (r + u)) : Fin (k + r) ≃ Fin (r + (u + r)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (σ.trans finSumFinEquiv.symm) (Equiv.refl (Fin r))).trans
    ((Equiv.sumAssoc (Fin r) (Fin u) (Fin r)).trans
      ((Equiv.sumCongr (Equiv.refl (Fin r)) finSumFinEquiv).trans finSumFinEquiv)))

/-- **A branch at a read outcome string**, on any input: the referee on `f`, its read outcome bits
evaluated at `o`, its data bits first and its unread outcome bits kept as the last `u` bits. T14's
`Protocol.branch` evaluates every outcome bit of the interpretation of a carrier state; this one
evaluates the read ones only, through the referee, so its input is any amplitude function. -/
noncomputable def readBranch {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (f : (Fin n → ZMod 2) → ℂ) (o : Fin r → ZMod 2) : (Fin (n + u) → ZMod 2) → ℂ :=
  fun v => p.interpretAmp f
    (Fin.append (v ∘ Fin.castAdd u) (Fin.append o (v ∘ Fin.natAdd n) ∘ σ))

/-! ## The proofs' lemmas

### The Choi amplitude: the letters on the second half -/

/-- The doubled word `(x, v)` read at a moved bit is `v` at that bit. -/
private theorem doubled_secondHalfBit {n k : ℕ} (x : Fin n → ZMod 2) (v : Fin (n + k) → ZMod 2)
    (i : Fin (n + k)) :
    (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n k)) (secondHalfBit n k i) = v i := by
  simp only [Function.comp_apply, secondHalfBit, Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]

/-- The doubled word `(x, v)` read through `secondHalfBit` is `v`. -/
private theorem doubled_comp_secondHalfBit {n k : ℕ} (x : Fin n → ZMod 2)
    (v : Fin (n + k) → ZMod 2) :
    (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n k)) ∘ secondHalfBit n k = v := by
  funext i
  exact doubled_secondHalfBit x v i

/-- Updating the doubled word `(x, v)` at a moved bit updates `v`. -/
private theorem update_doubled {n k : ℕ} (x : Fin n → ZMod 2) (v : Fin (n + k) → ZMod 2)
    (i : Fin (n + k)) (b : ZMod 2) :
    Function.update (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n k)) (secondHalfBit n k i) b
      = Fin.append x (Function.update v i b) ∘ Fin.cast (Nat.add_assoc n n k) := by
  rw [← update_append_natAdd,
    show Fin.natAdd n i = Fin.cast (Nat.add_assoc n n k) (secondHalfBit n k i) by
      simp only [secondHalfBit, Fin.cast_cast, Fin.cast_eq_self],
    Function.update_comp_eq_of_injective _ (Fin.cast_injective _)]

/-- A moved letter acts on the second half alone: at `(x, v)` it is the letter on the slice at
`x`. -/
private theorem letterAmp_secondHalfLetter {n k M : ℕ} (l : GateLetter (n + k) M)
    (F : (Fin ((n + n) + k) → ZMod 2) → ℂ) (x : Fin n → ZMod 2) :
    (fun v => letterAmp (secondHalfLetter n l) F (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n k)))
      = letterAmp l (fun v => F (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n k))) := by
  funext v
  cases l with
  | hadamard i =>
    simp only [secondHalfLetter, letterAmp]
    unfold walshTransform
    rw [update_doubled, update_doubled, doubled_secondHalfBit]
  | diagonal D =>
    change charOf M (DiagPhase.eval (MvPolynomial.rename (secondHalfBit n k) D) _) * F _
      = charOf M (DiagPhase.eval D v) * F _
    rw [DiagPhase.eval_rename, doubled_comp_secondHalfBit]
  | cnot i j hij =>
    change F (DiagPhase.cnotBitMap (secondHalfBit n k i) (secondHalfBit n k j) _)
      = F (Fin.append x (DiagPhase.cnotBitMap i j v) ∘ _)
    unfold DiagPhase.cnotBitMap
    rw [doubled_secondHalfBit, doubled_secondHalfBit, update_doubled]

/-- A moved word acts on the second half alone, letter by letter. -/
private theorem runAmp_secondHalf {n k M : ℕ} (w : GateWord (n + k) M)
    (F : (Fin ((n + n) + k) → ZMod 2) → ℂ) (x : Fin n → ZMod 2) (v : Fin (n + k) → ZMod 2) :
    runAmp (w.map (secondHalfLetter n)) F (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n k))
      = runAmp w (fun u => F (Fin.append x u ∘ Fin.cast (Nat.add_assoc n n k))) v := by
  induction w generalizing F with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, runAmp_cons, runAmp_cons, ih, letterAmp_secondHalfLetter]

/-- A sum over the doubled register, read through the cast, is a sum over `n + (n + k)`. -/
private theorem sum_doubled {n k : ℕ} (g : Fin (n + (n + k)) → ℕ) :
    ∑ j : Fin ((n + n) + k), g (Fin.cast (Nat.add_assoc n n k) j) = ∑ j, g j :=
  Fintype.sum_equiv (finCongr (Nat.add_assoc n n k)) _ _ (fun _ => rfl)

/-- The Z-dot of a moved Pauli reads the second half alone. -/
private theorem zDot_secondHalfPauli {n k : ℕ} (P : SignedPauli (n + k)) (x : Fin n → ZMod 2)
    (u : Fin (n + k) → ZMod 2) :
    zDot (secondHalfPauli n P).pauli (Fin.append x u ∘ Fin.cast (Nat.add_assoc n n k))
      = zDot P.pauli u := by
  unfold zDot secondHalfPauli
  simp only [Function.comp_apply]
  rw [sum_doubled (fun j => (Fin.append (0 : Fin n → ZMod 2) P.pauli.Z j).val
    * (Fin.append x u j).val), Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, ZMod.val_zero, zero_mul,
    Finset.sum_const_zero, zero_add]

/-- Adding a moved Pauli's X part to `(x, u)` adds the Pauli's X part to `u`. -/
private theorem doubled_add_X {n k : ℕ} (P : SignedPauli (n + k)) (x : Fin n → ZMod 2)
    (u : Fin (n + k) → ZMod 2) :
    Fin.append x u ∘ Fin.cast (Nat.add_assoc n n k) + (secondHalfPauli n P).pauli.X
      = Fin.append x (u + P.pauli.X) ∘ Fin.cast (Nat.add_assoc n n k) := by
  funext j
  simp only [secondHalfPauli, Pi.add_apply, Function.comp_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) (Fin.cast (Nat.add_assoc n n k) j)
  · simp only [Fin.append_left, Pi.zero_apply, add_zero]
  · simp only [Fin.append_right, Pi.add_apply]

/-- The projection of a moved Pauli at `(x, v)` is the Pauli's projection on the slice at `x`. -/
private theorem pauliProjection_secondHalfPauli {n k : ℕ} (P : SignedPauli (n + k)) (b : ZMod 2)
    (F : (Fin ((n + n) + k) → ZMod 2) → ℂ) (x : Fin n → ZMod 2) (v : Fin (n + k) → ZMod 2) :
    pauliProjection (secondHalfPauli n P) b F (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n k))
      = pauliProjection P b (fun u => F (Fin.append x u ∘ Fin.cast (Nat.add_assoc n n k))) v := by
  rw [pauliProjection_apply, pauliProjection_apply, doubled_add_X]
  unfold shiftFactor
  rw [yWeight_secondHalfPauli, doubled_add_X, zDot_secondHalfPauli]
  rfl

/-- The last bit of the doubled word `(x, v)` is the last bit of `v`. -/
private theorem last_doubled {n k : ℕ} (x : Fin n → ZMod 2) (v : Fin (n + (k + 1)) → ZMod 2) :
    (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n (k + 1))) (Fin.last (n + n + k))
      = v (Fin.last (n + k)) := by
  have h : Fin.cast (Nat.add_assoc n n (k + 1)) (Fin.last (n + n + k))
      = Fin.natAdd n (Fin.last (n + k)) := Fin.ext (by simp; omega)
  rw [Function.comp_apply, h, Fin.append_right]

/-- The doubled word `(x, v)` without its last bit is `(x, v)` with `v` without its last bit. -/
private theorem init_doubled {n k : ℕ} (x : Fin n → ZMod 2) (v : Fin (n + (k + 1)) → ZMod 2) :
    Fin.init (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n (k + 1)) : Fin (n + n + k + 1) → ZMod 2)
      = Fin.append x (Fin.init v) ∘ Fin.cast (Nat.add_assoc n n k) := by
  funext j
  obtain ⟨j0, rfl⟩ : ∃ j0, j = Fin.cast (Nat.add_assoc n n k).symm j0 :=
    ⟨Fin.cast (Nat.add_assoc n n k) j, by simp⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j0
  · have e : Fin.cast (Nat.add_assoc n n (k + 1))
        (Fin.castSucc (Fin.cast (Nat.add_assoc n n k).symm (Fin.castAdd (n + k) i)))
        = Fin.castAdd (n + (k + 1)) i := Fin.ext rfl
    simp only [Fin.init, Function.comp_apply, e, Fin.append_left, Fin.cast_cast,
      Fin.cast_eq_self]
    exact (Fin.append_left _ _ _).symm
  · have e : Fin.cast (Nat.add_assoc n n (k + 1))
        (Fin.castSucc (Fin.cast (Nat.add_assoc n n k).symm (Fin.natAdd n i)))
        = Fin.natAdd n (Fin.castSucc i) := Fin.ext rfl
    simp only [Fin.init, Function.comp_apply, e, Fin.append_right, Fin.cast_cast,
      Fin.cast_eq_self]

/-- **The referee on the second half.** At `(x, v)` the moved protocol's referee is `p`'s on the
slice of its input at `x`: the first `n` bits are spectators of every moved letter. -/
private theorem interpretAmp_onSecondHalf {m n k : ℕ} (p : Protocol m n k)
    (F : (Fin (n + n) → ZMod 2) → ℂ) (x : Fin n → ZMod 2) (v : Fin (n + k) → ZMod 2) :
    p.onSecondHalf.interpretAmp F (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n k))
      = p.interpretAmp (fun u => F (Fin.append x u)) v := by
  induction p with
  | nil => rfl
  | word p w ih =>
    have e : (p.word w).onSecondHalf = p.onSecondHalf.word (w.map (secondHalfLetter n)) := rfl
    rw [e, Protocol.interpretAmp_word, Protocol.interpretAmp_word, runAmp_secondHalf]
    congr 1
    funext u
    exact ih u
  | condition p P hP ih =>
    have e : (p.condition P hP).onSecondHalf = p.onSecondHalf.condition (secondHalfPauli n P)
        (by rw [yWeight_secondHalfPauli]; exact hP) := rfl
    rw [e, Protocol.interpretAmp_condition, Protocol.interpretAmp_condition]
    beta_reduce
    rw [last_doubled, init_doubled, pauliProjection_secondHalfPauli]
    congr 1
    funext u
    exact ih u

-- source: papers/categorical_qm/
-- Backens_2014_zx_calculus_complete_stabilizer_1307.7025 theorem:thm:Choi-Jamiolkowski
/-- The Choi amplitude at `(x, v)` is the referee on `δ_x` at `v`: the operator's input bent into
the reference bits, on the Bell floor (`amp_interpret`, `interpretAmp_onSecondHalf`). -/
private theorem amp_choi_doubled {m n k : ℕ} (p : Protocol m n k) (hm : 1 ≤ m) (x : Fin n → ZMod 2)
    (v : Fin (n + k) → ZMod 2) :
    amp (choi p) (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n k))
      = p.interpretAmp (delta x) v := by
  have hS : IsCarrier (idAt n m) := isCarrier_liftPrecision (isCarrier_idState n) _ _
  have hSm : (idAt n m).m = m := max_eq_right hm
  unfold choi
  rw [(amp_interpret _ hS hSm).2, interpretAmp_onSecondHalf]
  congr 1
  funext u
  unfold idAt delta
  rw [amp_liftPrecision, amp_idState]
  simp only [append_comp_castAdd, append_comp_natAdd]
  by_cases h : u = x
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun h' => h h'.symm), if_neg h]

/-! ### Channel equality on Gram data -/

/-- The channel's Gram data at the input pair `(x, x')` and the output pair `(a, b)`:
`Σ_e V(a, e) x · conj (V(b, e) x')`, the unread bits summed. -/
private noncomputable def choiGram {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (x : Fin n → ZMod 2) (a : (Fin n → ZMod 2) × (Fin r → ZMod 2)) (x' : Fin n → ZMod 2)
    (b : (Fin n → ZMod 2) × (Fin r → ZMod 2)) : ℂ :=
  ∑ e : Fin u → ZMod 2, dilation p σ (a, e) x * starRingEnd ℂ (dilation p σ (b, e) x')

/-- The channel's entry at `(a, b)` on `ρ` is `Σ_{x, x'} ρ(x, x') · G(x, a; x', b)`. -/
private theorem channel_apply {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (a b : (Fin n → ZMod 2) × (Fin r → ZMod 2)) :
    channel p σ ρ a b = ∑ x, ∑ x', ρ x x' * choiGram p σ x a x' b := by
  unfold channel choiGram
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun x' _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ =>
    Finset.sum_congr rfl fun e _ => ?_
  ring

/-- Two channels are equal exactly when their Gram data are: the channel is linear in `ρ`, and on
`∣x⟩⟨x'∣` it is the Gram data at `(x, x')`. -/
private theorem channel_eq_iff_choiGram {m m' n k k' r u u' : ℕ} (p : Protocol m n k)
    (q : Protocol m' n k') (σ : Fin k ≃ Fin (r + u)) (τ : Fin k' ≃ Fin (r + u')) :
    channel p σ = channel q τ ↔ choiGram p σ = choiGram q τ := by
  constructor
  · intro h
    funext x a x' b
    have hab := congrFun (congrFun (congrFun h (fun y y' => if y = x ∧ y' = x' then 1 else 0)) a) b
    rw [channel_apply, channel_apply] at hab
    simpa only [ite_mul, one_mul, zero_mul, ite_and, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_ite_irrel, Finset.sum_const_zero] using hab
  · intro h
    funext ρ a b
    rw [channel_apply, channel_apply, h]

/-- The register of the Choi state read through `σ`, its reference bits `x`, data bits `y` and
read outcome bits `o`, against the protocol's register. -/
private theorem append_comp_readingEquiv {n k r u : ℕ} (σ : Fin k ≃ Fin (r + u))
    (X : Fin ((n + n) + r) → ZMod 2) (e : Fin u → ZMod 2) :
    Fin.append X e ∘ readingEquiv (n + n) σ
      = Fin.append ((X ∘ Fin.castAdd r) ∘ Fin.castAdd n)
          (Fin.append ((X ∘ Fin.castAdd r) ∘ Fin.natAdd n)
            (Fin.append (X ∘ Fin.natAdd (n + n)) e ∘ σ))
        ∘ Fin.cast (Nat.add_assoc n n k) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have e1 : readingEquiv (n + n) σ (Fin.castAdd k j) = Fin.castAdd u (Fin.castAdd r j) := by
      simp only [readingEquiv, Equiv.coe_trans, Function.comp_apply,
        finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl, Equiv.coe_refl,
        id_eq, finSumFinEquiv_apply_left, finCongr_apply]
      exact Fin.ext rfl
    rw [Function.comp_apply, Function.comp_apply, e1, Fin.append_left]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · have e2 : Fin.cast (Nat.add_assoc n n k) (Fin.castAdd k (Fin.castAdd n l))
          = Fin.castAdd (n + k) l := Fin.ext rfl
      rw [e2, Fin.append_left]
      rfl
    · have e2 : Fin.cast (Nat.add_assoc n n k) (Fin.castAdd k (Fin.natAdd n l))
          = Fin.natAdd n (Fin.castAdd k l) := Fin.ext rfl
      rw [e2, Fin.append_right, Fin.append_left]
      rfl
  · have e1 : readingEquiv (n + n) σ (Fin.natAdd (n + n) j)
        = Fin.cast (Nat.add_assoc (n + n) r u).symm (Fin.natAdd (n + n) (σ j)) := by
      simp only [readingEquiv, Equiv.coe_trans, Function.comp_apply,
        finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
        finSumFinEquiv_apply_right, finCongr_apply]
    have e2 : Fin.cast (Nat.add_assoc n n k) (Fin.natAdd (n + n) j)
        = Fin.natAdd n (Fin.natAdd n j) := Fin.ext (by simp; omega)
    rw [Function.comp_apply, Function.comp_apply, e1, e2, Fin.append_right, Fin.append_right,
      Function.comp_apply]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) (σ j)
    · have e3 : Fin.cast (Nat.add_assoc (n + n) r u).symm (Fin.natAdd (n + n) (Fin.castAdd u l))
          = Fin.castAdd u (Fin.natAdd (n + n) l) := Fin.ext rfl
      rw [e3, Fin.append_left, Fin.append_left]
      rfl
    · have e3 : Fin.cast (Nat.add_assoc (n + n) r u).symm (Fin.natAdd (n + n) (Fin.natAdd r l))
          = Fin.natAdd (n + n + r) l := Fin.ext (by simp; omega)
      rw [e3, Fin.append_right, Fin.append_right]

/-- The amplitude of the Choi state read through `σ` (`amp_reindexFreeBits`). -/
private theorem amp_choiRead {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u)) :
    amp (choiRead p σ) = fun w => amp (choi p) (w ∘ readingEquiv (n + n) σ) :=
  amp_reindexFreeBits _ _ _

/-- The Gram data of the Choi state read through `σ` at `((x, y, o), (x', y', o'))` is the
channel's Gram data at `(x, (y, o); x', (y', o'))`. -/
private theorem gram_choiRead {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (hm : 1 ≤ m) (X Y : Fin ((n + n) + r) → ZMod 2) :
    gram (amp (choiRead p σ)) X Y
      = choiGram p σ ((X ∘ Fin.castAdd r) ∘ Fin.castAdd n)
          ((X ∘ Fin.castAdd r) ∘ Fin.natAdd n, X ∘ Fin.natAdd (n + n))
          ((Y ∘ Fin.castAdd r) ∘ Fin.castAdd n)
          ((Y ∘ Fin.castAdd r) ∘ Fin.natAdd n, Y ∘ Fin.natAdd (n + n)) := by
  unfold gram choiGram dilation
  simp only [amp_choiRead, append_comp_readingEquiv, amp_choi_doubled p hm]

/-- Choi states with equal Gram data at any numbers of unread bits exactly when the channels are
equal: `choi_gram_eq_iff`, before its place in the statement. -/
private theorem gram_choiRead_eq_iff {m m' n k k' r u u' : ℕ} (p : Protocol m n k)
    (q : Protocol m' n k') (σ : Fin k ≃ Fin (r + u)) (τ : Fin k' ≃ Fin (r + u')) (hm : 1 ≤ m)
    (hm' : 1 ≤ m') :
    (∀ x y : Fin ((n + n) + r) → ZMod 2,
        gram (amp (choiRead p σ)) x y = gram (amp (choiRead q τ)) x y)
      ↔ channel p σ = channel q τ := by
  rw [channel_eq_iff_choiGram]
  constructor
  · intro h
    funext x a x' b
    have hab := h (Fin.append (Fin.append x a.1) a.2) (Fin.append (Fin.append x' b.1) b.2)
    simpa only [gram_choiRead p σ hm, gram_choiRead q τ hm', append_comp_castAdd,
      append_comp_natAdd] using hab
  · intro h X Y
    rw [gram_choiRead p σ hm, gram_choiRead q τ hm', h]


/-! ### The measured reading -/

/-- A word on `t + 1` bits is fixed by its first `t` bits and its last. -/
private theorem eq_iff_init_last {t : ℕ} (c g : Fin (t + 1) → ZMod 2) :
    c = g ↔ Fin.init c = Fin.init g ∧ c (Fin.last t) = g (Fin.last t) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← Fin.snoc_init_self c, ← Fin.snoc_init_self g, h1, h2]

/-- `(y, z, c)` without its last bit is `(y, z, c)` with `c` without its last bit. -/
private theorem init_append_append {n k t : ℕ} (y : Fin n → ZMod 2) (z : Fin k → ZMod 2)
    (c : Fin (t + 1) → ZMod 2) :
    Fin.init (Fin.append y (Fin.append z c) : Fin (n + (k + (t + 1))) → ZMod 2)
      = Fin.append y (Fin.append z (Fin.init c)) := by
  funext i
  change Fin.append y (Fin.append z c) (Fin.castSucc (i : Fin (n + (k + t))))
    = Fin.append y (Fin.append z (Fin.init c)) i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · have e : (Fin.castSucc (Fin.castAdd (k + t) l) : Fin (n + (k + t) + 1))
        = Fin.castAdd (k + (t + 1)) l := Fin.ext rfl
    change Fin.append y (Fin.append z c) (Fin.castSucc (Fin.castAdd (k + t) l))
      = Fin.append y (Fin.append z (Fin.init c)) (Fin.castAdd (k + t) l)
    rw [e, Fin.append_left, Fin.append_left]
  · refine Fin.addCases (fun l' => ?_) (fun l' => ?_) l
    · have e : (Fin.castSucc (Fin.natAdd n (Fin.castAdd t l')) : Fin (n + (k + t) + 1))
          = Fin.natAdd n (Fin.castAdd (t + 1) l') := Fin.ext rfl
      change Fin.append y (Fin.append z c) (Fin.castSucc (Fin.natAdd n (Fin.castAdd t l')))
        = Fin.append y (Fin.append z (Fin.init c)) (Fin.natAdd n (Fin.castAdd t l'))
      rw [e, Fin.append_right, Fin.append_right, Fin.append_left, Fin.append_left]
    · have e : (Fin.castSucc (Fin.natAdd n (Fin.natAdd k l')) : Fin (n + (k + t) + 1))
          = Fin.natAdd n (Fin.natAdd k (Fin.castSucc l')) := Fin.ext rfl
      change Fin.append y (Fin.append z c) (Fin.castSucc (Fin.natAdd n (Fin.natAdd k l')))
        = Fin.append y (Fin.append z (Fin.init c)) (Fin.natAdd n (Fin.natAdd k l'))
      rw [e, Fin.append_right, Fin.append_right, Fin.append_right, Fin.append_right]
      rfl

/-- The last bit of `(y, z, c)` is the last bit of `c`. -/
private theorem last_append_append {n k t : ℕ} (y : Fin n → ZMod 2) (z : Fin k → ZMod 2)
    (c : Fin (t + 1) → ZMod 2) :
    Fin.append y (Fin.append z c) (Fin.last (n + (k + t))) = c (Fin.last t) := by
  have e : (Fin.last (n + (k + t)) : Fin (n + (k + t) + 1))
      = Fin.natAdd n (Fin.natAdd k (Fin.last t)) :=
    Fin.ext (by simp only [Fin.val_last, Fin.val_natAdd])
  simp only [e, Fin.append_right]

/-- **The copies.** After `t` copies, the referee at `(y, z, c)` is `p`'s at `(y, z)` when each
copy `c s` equals the read outcome bit it copies, and `0` otherwise
(`pauliProjection_zPauli_single`). -/
private theorem interpretAmp_copyReadBits {m n k r u : ℕ} (p : Protocol m n k)
    (σ : Fin k ≃ Fin (r + u)) (f : (Fin n → ZMod 2) → ℂ) :
    ∀ (t : ℕ) (ht : t ≤ r) (y : Fin n → ZMod 2) (z : Fin k → ZMod 2) (c : Fin t → ZMod 2),
      (copyReadBits p σ t ht).interpretAmp f (Fin.append y (Fin.append z c))
        = if c = (fun s => z (σ.symm (Fin.castAdd u (Fin.castLE ht s))))
          then p.interpretAmp f (Fin.append y z) else 0
  | 0, ht, y, z, c => by
    rw [if_pos (Subsingleton.elim _ _)]
    have hz : Fin.append z c = z := funext fun i => Fin.append_left z c i
    change p.interpretAmp f (Fin.append y (Fin.append z c)) = _
    rw [hz]
  | t + 1, ht, y, z, c => by
    have e : copyReadBits p σ (t + 1) ht = (copyReadBits p σ t (Nat.le_of_succ_le ht)).condition
        ⟨0, zPauli (Pi.single (Fin.natAdd n (Fin.castAdd t (σ.symm (Fin.castAdd u ⟨t, ht⟩)))) 1)⟩
        (zPauli_precision m _) := rfl
    rw [e, Protocol.interpretAmp_condition]
    beta_reduce
    rw [last_append_append, init_append_append, pauliProjection_zPauli_single, Fin.append_right,
      Fin.append_left, interpretAmp_copyReadBits p σ f t (Nat.le_of_succ_le ht)]
    have key := eq_iff_init_last c (fun s => z (σ.symm (Fin.castAdd u (Fin.castLE ht s))))
    by_cases h1 : Fin.init c
        = fun s => z (σ.symm (Fin.castAdd u (Fin.castLE (Nat.le_of_succ_le ht) s)))
    · by_cases h2 : z (σ.symm (Fin.castAdd u ⟨t, ht⟩)) = c (Fin.last t)
      · rw [if_pos h2, if_pos h1, if_pos (key.mpr ⟨h1, h2.symm⟩)]
      · rw [if_neg h2, if_neg (fun h => h2 (key.mp h).2.symm)]
    · rw [if_neg (fun h => h1 (key.mp h).1)]
      split_ifs <;> rfl

/-- The measured reading: the outcome word `(o, e)` read through `measuredReading σ` is the reading
`σ` of `(o, e)`'s first `u` unread bits, then the copies, the last `r`. -/
private theorem append_comp_measuredReading {k r u : ℕ} (σ : Fin k ≃ Fin (r + u))
    (o : Fin r → ZMod 2) (e : Fin (u + r) → ZMod 2) :
    Fin.append o e ∘ measuredReading σ
      = Fin.append (Fin.append o (e ∘ Fin.castAdd r) ∘ σ) (e ∘ Fin.natAdd u) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left, Function.comp_apply, Function.comp_apply]
    refine Fin.addCases (motive := fun s => σ j = s → _) (fun a ha => ?_) (fun b hb => ?_) (σ j) rfl
    · simp only [measuredReading, Equiv.coe_trans, Function.comp_apply,
        finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl, ha,
        Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, Equiv.coe_refl, id_eq,
        finSumFinEquiv_apply_left, Fin.append_left]
    · simp only [measuredReading, Equiv.coe_trans, Function.comp_apply,
        finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl, hb,
        finSumFinEquiv_symm_apply_natAdd, Equiv.sumAssoc_apply_inl_inr, Sum.map_inr,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.append_right]
  · simp only [measuredReading, Equiv.coe_trans, Function.comp_apply,
      finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr, Equiv.coe_refl, id_eq,
      Equiv.sumAssoc_apply_inr, finSumFinEquiv_apply_right, Fin.append_right]

/-- The measured dilation is the dilation where the copies equal the read outcome string, and `0`
elsewhere. -/
private theorem dilation_measured {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (y : Fin n → ZMod 2) (o : Fin r → ZMod 2) (e : Fin (u + r) → ZMod 2) (x : Fin n → ZMod 2) :
    dilation (measured p σ) (measuredReading σ) ((y, o), e) x
      = if e ∘ Fin.natAdd u = o then dilation p σ ((y, o), e ∘ Fin.castAdd r) x else 0 := by
  unfold dilation measured
  rw [append_comp_measuredReading, interpretAmp_copyReadBits]
  have hg : (fun s : Fin r => (Fin.append o (e ∘ Fin.castAdd r) ∘ σ)
      (σ.symm (Fin.castAdd u (Fin.castLE le_rfl s)))) = o := by
    funext s
    rw [Function.comp_apply, Equiv.apply_symm_apply]
    exact Fin.append_left _ _ _
  rw [hg]

/-- The measured Gram data vanish off the diagonal of the read outcome strings and are the
channel's on it. -/
private theorem choiGram_measured {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (x x' y y' : Fin n → ZMod 2) (o o' : Fin r → ZMod 2) :
    choiGram (measured p σ) (measuredReading σ) x (y, o) x' (y', o')
      = if o = o' then choiGram p σ x (y, o) x' (y', o) else 0 := by
  unfold choiGram
  have hsplit : ∀ G : (Fin (u + r) → ZMod 2) → ℂ,
      ∑ e', G e' = ∑ e : Fin u → ZMod 2, ∑ c : Fin r → ZMod 2, G (Fin.append e c) := fun G => by
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv (Fin.appendEquiv u r) _ _ (fun _ => rfl)).symm
  rw [hsplit]
  simp only [dilation_measured, append_comp_castAdd, append_comp_natAdd]
  by_cases ho : o = o'
  · subst ho
    rw [if_pos rfl]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_eq_single o (fun c _ hc => by rw [if_neg hc, zero_mul])
      (fun h => absurd (Finset.mem_univ o) h), if_pos rfl, if_pos rfl]
  · rw [if_neg ho]
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c = o
    · rw [if_neg (fun h => ho (hc.symm.trans h)), map_zero, mul_zero]
    · rw [if_neg hc, zero_mul]

/-- The referee on `f` is `Σ_x f(x)` times the referee on `δ_x` (`interpretAmp_add_smul`). -/
private theorem interpretAmp_eq_sum {m n k : ℕ} (p : Protocol m n k) (f : (Fin n → ZMod 2) → ℂ)
    (w : Fin (n + k) → ZMod 2) :
    p.interpretAmp f w = ∑ x, f x * p.interpretAmp (delta x) w := by
  have hzero : p.interpretAmp 0 = 0 := by
    have h := interpretAmp_add_smul p 0 0 (-1)
    rwa [smul_zero, add_zero, neg_one_smul, add_neg_cancel] at h
  have hsum : ∀ s : Finset (Fin n → ZMod 2),
      p.interpretAmp (∑ x ∈ s, f x • delta x) = ∑ x ∈ s, f x • p.interpretAmp (delta x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, hzero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm (f a • delta a),
        interpretAmp_add_smul, ih, add_comm (∑ x ∈ s, f x • p.interpretAmp (delta x))]
  have hf : f = ∑ x, f x • delta x := by
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, delta, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  calc p.interpretAmp f w = p.interpretAmp (∑ x, f x • delta x) w := by rw [← hf]
    _ = ∑ x, f x * p.interpretAmp (delta x) w := by
      rw [hsum, Finset.sum_apply]
      rfl

/-- The Gram data of a branch on `f` is the channel's Gram data at the read outcome string, paired
with `f(x) · conj (f(x'))`. -/
private theorem gram_readBranch {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (f : (Fin n → ZMod 2) → ℂ) (o : Fin r → ZMod 2) (y y' : Fin n → ZMod 2) :
    gram (readBranch p σ f o) y y'
      = ∑ x, ∑ x', f x * starRingEnd ℂ (f x') * choiGram p σ x (y, o) x' (y', o) := by
  unfold gram readBranch choiGram dilation
  simp only [append_comp_castAdd, append_comp_natAdd]
  simp only [interpretAmp_eq_sum p f, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ =>
    Finset.sum_congr rfl fun e _ => ?_
  ring

/-- Polarization: the form `f ↦ Σ f(x) · conj (f(x')) · A(x, x')` on every `f` determines `A`. -/
private theorem sesquilinear_eq_iff {α : Type*} [Fintype α] (A B : α → α → ℂ) :
    (∀ f : α → ℂ, ∑ x, ∑ x', f x * starRingEnd ℂ (f x') * A x x'
        = ∑ x, ∑ x', f x * starRingEnd ℂ (f x') * B x x') ↔ A = B := by
  classical
  constructor
  · intro h
    have hexp : ∀ (a b : α) (c : ℂ),
        ∑ x, ∑ x', ((if x = a then 1 else 0) + c * (if x = b then 1 else 0))
            * starRingEnd ℂ ((if x' = a then 1 else 0) + c * (if x' = b then 1 else 0))
            * (A x x' - B x x')
          = (A a a - B a a) + starRingEnd ℂ c * (A a b - B a b) + c * (A b a - B b a)
            + c * starRingEnd ℂ c * (A b b - B b b) := by
      intro a b c
      simp only [map_add, apply_ite (starRingEnd ℂ), map_one, map_zero, add_mul,
        mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have hzero : ∀ (a b : α) (c : ℂ),
        (A a a - B a a) + starRingEnd ℂ c * (A a b - B a b) + c * (A b a - B b a)
            + c * starRingEnd ℂ c * (A b b - B b b) = 0 := by
      intro a b c
      rw [← hexp]
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [h, sub_self]
    funext a b
    have h0 := hzero a a 0
    have h0' := hzero b b 0
    simp only [map_zero, zero_mul, add_zero] at h0 h0'
    have h1 := hzero a b 1
    have hI := hzero a b Complex.I
    rw [h0, h0'] at h1 hI
    simp only [map_one, one_mul, mul_zero, add_zero, zero_add, Complex.conj_I] at h1 hI
    have : A a b - B a b = 0 := by
      linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * hI
        + ((A a b - B a b) - (A b a - B b a)) / 2 * Complex.I_sq
    exact sub_eq_zero.mp this
  · rintro rfl _
    rfl

/-! ### The ring condition: every letter's entries in `ℤ[ζ_{2^∞}, ½]`

The first five lemmas restate private lemmas of `FTQCLib.Carrier.UnreadBits`, with the same names
and proofs. -/

/-- A root of unity of order a power of two lies in the ring. -/
private theorem mem_dyadicCyclotomicRing_of_pow {z : ℂ} {M : ℕ} (h : z ^ 2 ^ M = 1) :
    z ∈ dyadicCyclotomicRing :=
  Subring.subset_closure (Or.inr ⟨M, h⟩)

/-- `½` lies in the ring. -/
private theorem inv_two_mem_dyadicCyclotomicRing : (2 : ℂ)⁻¹ ∈ dyadicCyclotomicRing :=
  Subring.subset_closure (Or.inl rfl)

/-- A character value is a root of unity of order a power of two. -/
private theorem charOf_mem_dyadicCyclotomicRing (m : ℕ) (z : ZMod (2 ^ m)) :
    charOf m z ∈ dyadicCyclotomicRing := by
  refine mem_dyadicCyclotomicRing_of_pow (M := m) ?_
  rw [charOf_eq_zeta_pow, ← pow_mul, mul_comm, pow_mul, (isPrimitiveRoot_zeta m).pow_eq_one,
    one_pow]

/-- `1/√2 = ½(ζ₈ + ζ₈⁻¹)` lies in the ring. -/
private theorem one_div_sqrt_two_mem_dyadicCyclotomicRing :
    1 / (Real.sqrt 2 : ℂ) ∈ dyadicCyclotomicRing := by
  have hsum : charOf 3 1 + charOf 3 (-1) = (Real.sqrt 2 : ℂ) := by
    rw [charOf_three_one, charOf_three_neg_one, ← add_div,
      show (1 + Complex.I + (1 - Complex.I)) = (2 : ℂ) by ring, div_eq_iff ofReal_sqrt_two_ne_zero,
      ← sq, sqrt_two_sq_complex]
  have h : 1 / (Real.sqrt 2 : ℂ) = (2 : ℂ)⁻¹ * (charOf 3 1 + charOf 3 (-1)) := by
    rw [hsum, eq_inv_mul_iff_mul_eq₀ two_ne_zero, ← sqrt_two_sq_complex, sq, mul_assoc, one_div,
      mul_inv_cancel₀ ofReal_sqrt_two_ne_zero, mul_one]
  rw [h]
  exact Subring.mul_mem _ inv_two_mem_dyadicCyclotomicRing
    (Subring.add_mem _ (charOf_mem_dyadicCyclotomicRing 3 1)
      (charOf_mem_dyadicCyclotomicRing 3 (-1)))

/-- A Walsh sign lies in the ring. -/
private theorem signOf_mem_dyadicCyclotomicRing (b : ZMod 2) :
    signOf b ∈ dyadicCyclotomicRing := by
  unfold signOf
  split
  · exact Subring.one_mem _
  · exact Subring.neg_mem _ (Subring.one_mem _)

/-- Every power of `−1` lies in the ring. -/
private theorem neg_one_pow_mem_dyadicCyclotomicRing (e : ℕ) :
    (-1 : ℂ) ^ e ∈ dyadicCyclotomicRing :=
  Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) e

/-- Every power of `i` lies in the ring: `i` is a root of unity of order `4`. -/
private theorem I_pow_mem_dyadicCyclotomicRing (e : ℕ) :
    Complex.I ^ e ∈ dyadicCyclotomicRing :=
  Subring.pow_mem _ (mem_dyadicCyclotomicRing_of_pow (M := 2) (by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact Complex.I_pow_four)) e

/-- A point mass takes its values `0` and `1` in the ring. -/
private theorem delta_mem_dyadicCyclotomicRing {N : ℕ} (x u : Fin N → ZMod 2) :
    delta x u ∈ dyadicCyclotomicRing := by
  unfold delta
  split
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

/-- A letter keeps values in the ring: `1/√2` and a sign for H, a root of unity for a diagonal
letter, a permutation for CNOT. -/
private theorem letterAmp_mem_dyadicCyclotomicRing {N M : ℕ} (g : GateLetter N M)
    {f : (Fin N → ZMod 2) → ℂ} (hf : ∀ w, f w ∈ dyadicCyclotomicRing) (w : Fin N → ZMod 2) :
    letterAmp g f w ∈ dyadicCyclotomicRing := by
  cases g with
  | hadamard i =>
    change 1 / (Real.sqrt 2 : ℂ)
      * (f (Function.update w i 0) + signOf (w i) * f (Function.update w i 1))
      ∈ dyadicCyclotomicRing
    exact Subring.mul_mem _ one_div_sqrt_two_mem_dyadicCyclotomicRing
      (Subring.add_mem _ (hf _) (Subring.mul_mem _ (signOf_mem_dyadicCyclotomicRing _) (hf _)))
  | diagonal D =>
    change charOf M (D.eval w) * f w ∈ dyadicCyclotomicRing
    exact Subring.mul_mem _ (charOf_mem_dyadicCyclotomicRing M _) (hf w)
  | cnot i j hij => exact hf _

/-- A word keeps values in the ring, letter by letter. -/
private theorem runAmp_mem_dyadicCyclotomicRing {N M : ℕ} (gs : GateWord N M) :
    ∀ {f : (Fin N → ZMod 2) → ℂ}, (∀ w, f w ∈ dyadicCyclotomicRing) →
      ∀ w, runAmp gs f w ∈ dyadicCyclotomicRing := by
  induction gs with
  | nil => exact fun hf => hf
  | cons g gs ih =>
    intro f hf w
    rw [runAmp_cons]
    exact ih (letterAmp_mem_dyadicCyclotomicRing g hf) w

/-- A projection `Π_b` keeps values in the ring: `½`, signs and powers of `i`. -/
private theorem pauliProjection_mem_dyadicCyclotomicRing {N : ℕ} (P : SignedPauli N) (b : ZMod 2)
    {f : (Fin N → ZMod 2) → ℂ} (hf : ∀ w, f w ∈ dyadicCyclotomicRing) (w : Fin N → ZMod 2) :
    pauliProjection P b f w ∈ dyadicCyclotomicRing := by
  rw [pauliProjection_apply, one_div]
  unfold shiftFactor
  exact Subring.mul_mem _ inv_two_mem_dyadicCyclotomicRing
    (Subring.add_mem _ (hf w) (Subring.mul_mem _
      (Subring.mul_mem _ (neg_one_pow_mem_dyadicCyclotomicRing _)
        (Subring.mul_mem _ (neg_one_pow_mem_dyadicCyclotomicRing _)
          (Subring.mul_mem _ (I_pow_mem_dyadicCyclotomicRing _)
            (neg_one_pow_mem_dyadicCyclotomicRing _))))
      (hf _)))

/-- **The referee keeps values in the ring**, letter by letter and projection by projection. -/
private theorem interpretAmp_mem_dyadicCyclotomicRing {m n k : ℕ} (p : Protocol m n k)
    {f : (Fin n → ZMod 2) → ℂ} (hf : ∀ w, f w ∈ dyadicCyclotomicRing) :
    ∀ v, p.interpretAmp f v ∈ dyadicCyclotomicRing := by
  induction p with
  | nil => exact hf
  | word p w ih =>
    intro v
    rw [Protocol.interpretAmp_word]
    exact runAmp_mem_dyadicCyclotomicRing w ih v
  | condition p P hP ih =>
    intro v
    rw [Protocol.interpretAmp_condition]
    exact pauliProjection_mem_dyadicCyclotomicRing P _ ih _

/-- Every word of the doubled register is `(x, v)` read through the cast, `x` its first `n` bits. -/
private theorem exists_doubled {n k : ℕ} (w : Fin ((n + n) + k) → ZMod 2) :
    ∃ (x : Fin n → ZMod 2) (v : Fin (n + k) → ZMod 2),
      Fin.append x v ∘ Fin.cast (Nat.add_assoc n n k) = w := by
  let g : Fin (n + (n + k)) → ZMod 2 := w ∘ Fin.cast (Nat.add_assoc n n k).symm
  have hg : Fin.append (g ∘ Fin.castAdd (n + k)) (g ∘ Fin.natAdd n) = g :=
    Fin.append_castAdd_natAdd
  refine ⟨g ∘ Fin.castAdd (n + k), g ∘ Fin.natAdd n, ?_⟩
  rw [hg]
  funext j
  simp only [g, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]

/-! ## The statement -/

/-- **Channel equality is equality up to unread bits of the Choi states** (the coherent reading).
Two protocols on the same `n` data bits, at any precisions `m, m' ≥ 1`, each read with `r` read and
`u` unread outcome bits, have Choi states equal up to their unread bits (T27's `UnreadEq u`, the
unread bits last and the reference, data and read outcome bits kept) exactly when their channels
`ρ ↦ Tr_unread (V ρ Vᴴ)` are equal. The read outcome bits are outputs kept coherently: this is not
equality branch by branch (`choi_measured_eq_iff`). Proved at T49.3. -/
theorem choi_eq_iff {m m' n k k' r u : ℕ} (p : Protocol m n k) (q : Protocol m' n k')
    (σ : Fin k ≃ Fin (r + u)) (τ : Fin k' ≃ Fin (r + u)) (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    UnreadEq u (choiRead p σ) (choiRead q τ) ↔ channel p σ = channel q τ :=
  gram_choiRead_eq_iff p q σ τ hm hm'

/-- **The measured reading is equality branch by branch.** With each read outcome bit copied into a
fresh unread bit (`measured`, `measuredReading`), two protocols on the same `n` data bits, at any
precisions `m, m' ≥ 1`, have Choi states equal up to their unread bits exactly when, at every read
outcome string `o` and on every input `f`, their branches have the same Gram data over the unread
bits (`gram`, T27). Every amplitude function is an input, through the referee. Proved at T49.3. -/
theorem choi_measured_eq_iff {m m' n k k' r u : ℕ} (p : Protocol m n k) (q : Protocol m' n k')
    (σ : Fin k ≃ Fin (r + u)) (τ : Fin k' ≃ Fin (r + u)) (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    UnreadEq (u + r) (choiRead (measured p σ) (measuredReading σ))
        (choiRead (measured q τ) (measuredReading τ))
      ↔ ∀ (f : (Fin n → ZMod 2) → ℂ) (o : Fin r → ZMod 2) (x y : Fin n → ZMod 2),
          gram (readBranch p σ f o) x y = gram (readBranch q τ f o) x y := by
  rw [choi_eq_iff _ _ _ _ hm hm', channel_eq_iff_choiGram]
  constructor
  · intro h f o y y'
    rw [gram_readBranch, gram_readBranch]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    have hx := congrFun (congrFun (congrFun (congrFun h x) (y, o)) x') (y', o)
    rw [choiGram_measured, choiGram_measured, if_pos rfl, if_pos rfl] at hx
    rw [hx]
  · intro h
    funext x a x' b
    obtain ⟨y, o⟩ := a
    obtain ⟨y', o'⟩ := b
    rw [choiGram_measured, choiGram_measured]
    by_cases ho : o = o'
    · subst ho
      rw [if_pos rfl, if_pos rfl]
      have hAB := (sesquilinear_eq_iff (fun x x' => choiGram p σ x (y, o) x' (y', o))
        (fun x x' => choiGram q τ x (y, o) x' (y', o))).mp (fun f => by
          rw [← gram_readBranch, ← gram_readBranch]
          exact h f o y y')
      exact congrFun (congrFun hAB x) x'
    · rw [if_neg ho, if_neg ho]

/-- **The ring condition of the tower.** The Choi amplitude of a protocol at precision `m ≥ 1`
takes every value in `ℤ[ζ_{2^∞}, ½]` (`dyadicCyclotomicRing`): the floor's values are `0` and
`1`, and every letter's matrix has its entries in the ring. A statement about `amp (choi p)`, not
about the carrier state's scale or bound sums, which may carry non-dyadic factors: carrier-ness of
a Choi state does not separate the tower (the `3/5` rotation). Proved at T49.3. -/
theorem choi_mem_dyadic {m n k : ℕ} (p : Protocol m n k) (hm : 1 ≤ m)
    (w : Fin ((n + n) + k) → ZMod 2) : amp (choi p) w ∈ dyadicCyclotomicRing := by
  obtain ⟨x, v, rfl⟩ := exists_doubled w
  rw [amp_choi_doubled p hm]
  exact interpretAmp_mem_dyadicCyclotomicRing p (delta_mem_dyadicCyclotomicRing x) v

/-! ## Added by restatement (docs/STEPS.md, entry 2026-10-02i) -/

/-- **The Choi state is a carrier state** at the protocol's precision `m ≥ 1`: T14's
interpretation keeps carrier states, and the lifted floor `idAt n m` is one (`isCarrier_idState`,
R7). Proved at T49.3.1. -/
theorem isCarrier_choi {m n k : ℕ} (p : Protocol m n k) (hm : 1 ≤ m) :
    IsCarrier (choi p) ∧ (choi p).m = m := by
  have hS : IsCarrier (idAt n m) := isCarrier_liftPrecision (isCarrier_idState n) _ _
  have hSm : (idAt n m).m = m := max_eq_right hm
  exact ⟨(amp_interpret _ hS hSm).1, interpret_m _ hm hSm⟩

/-- **The Choi amplitude.** At the reference word `x` and the protocol's word `v` (data bits, then
outcome bits), the Choi state's amplitude is the referee on the point mass `δ_x`, read at `v`: so
`choi p` determines `interpretAmp p` and conversely, by linearity (`interpretAmp_add_smul`).
Proved at T49.3.1. -/
theorem amp_choi {m n k : ℕ} (p : Protocol m n k) (hm : 1 ≤ m) (x : Fin n → ZMod 2)
    (v : Fin (n + k) → ZMod 2) :
    amp (choi p) (Fin.append x v ∘ Fin.cast (Nat.add_assoc n n k)) = p.interpretAmp (delta x) v :=
  amp_choi_doubled p hm x v

/-- **Channel equality across unread counts.** Two protocols on the same `n` data bits, at
precisions `m, m' ≥ 1`, read with `r` read outcome bits each and `u`, `u'` unread ones, have Choi
states with the same Gram data over their unread bits exactly when their channels are equal.
`gram` sums over the unread bits, so the two sides are functions of the same read words and no
padding is needed; `choi_eq_iff` is the case `u = u'`. Proved at T49.3.1. -/
theorem choi_gram_eq_iff {m m' n k k' r u u' : ℕ} (p : Protocol m n k) (q : Protocol m' n k')
    (σ : Fin k ≃ Fin (r + u)) (τ : Fin k' ≃ Fin (r + u')) (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    (∀ x y : Fin ((n + n) + r) → ZMod 2,
        gram (amp (choiRead p σ)) x y = gram (amp (choiRead q τ)) x y)
      ↔ channel p σ = channel q τ :=
  gram_choiRead_eq_iff p q σ τ hm hm'

/-- **The dilation is a dilation of the channel**: `channel p σ` is `dilation p σ` traced over the
unread outcome bits, the Stinespring form of D2's deferred measurement. Proved at T49.3.2. -/
theorem isDilation_dilation {m n k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u)) :
    IsDilation (channel p σ) (dilation p σ) :=
  fun _ => rfl

/-! ### Outside the tower: the dilation's entries and the rotation's Gram data -/

/-- Every entry of a protocol's dilation lies in the ring: it is a Choi amplitude (`amp_choi`,
`choi_mem_dyadic`). -/
private theorem dilation_mem_dyadicCyclotomicRing {m n k r u : ℕ} (p : Protocol m n k)
    (σ : Fin k ≃ Fin (r + u)) (hm : 1 ≤ m)
    (a : ((Fin n → ZMod 2) × (Fin r → ZMod 2)) × (Fin u → ZMod 2)) (x : Fin n → ZMod 2) :
    dilation p σ a x ∈ dyadicCyclotomicRing := by
  unfold dilation
  rw [← amp_choi p hm]
  exact choi_mem_dyadic p hm _

/-- The entry of `A ρ Aᴴ` at `(a, b)` is `Σ_{x, x'} ρ(x, x') · A(a, x) · conj (A(b, x'))`. -/
private theorem mul_mul_conjTranspose_apply {α β : Type*} [Fintype α] (A : Matrix β α ℂ)
    (ρ : Matrix α α ℂ) (a b : β) :
    (A * ρ * Aᴴ) a b = ∑ x, ∑ x', ρ x x' * (A a x * starRingEnd ℂ (A b x')) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  ring

/-- On the matrix unit at `(x, x')`, the sum `Σ_{y, y'} ρ(y, y') · G(y, y')` is `G(x, x')`. -/
private theorem sum_matrixUnit {α : Type*} [Fintype α] [DecidableEq α] (G : α → α → ℂ)
    (x x' : α) :
    ∑ y, ∑ y', (if y = x ∧ y' = x' then (1 : ℂ) else 0) * G y y' = G x x' := by
  simp only [ite_mul, one_mul, zero_mul, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]

/-- A protocol whose channel is the rotation's has the rotation's Gram data: at
`(x, a; x', b)`, `R(a, x) · conj (R(b, x'))`. -/
private theorem choiGram_of_channel_eq_rotation {m k u : ℕ} (p : Protocol m 1 k)
    (σ : Fin k ≃ Fin (0 + u))
    (h : channel p σ = fun ρ a b => (rotationThreeFifths * ρ * rotationThreeFifthsᴴ) a.1 b.1)
    (x : Fin 1 → ZMod 2) (a : (Fin 1 → ZMod 2) × (Fin 0 → ZMod 2)) (x' : Fin 1 → ZMod 2)
    (b : (Fin 1 → ZMod 2) × (Fin 0 → ZMod 2)) :
    choiGram p σ x a x' b
      = rotationThreeFifths a.1 x * starRingEnd ℂ (rotationThreeFifths b.1 x') := by
  have hab := congrFun (congrFun (congrFun h (fun y y' => if y = x ∧ y' = x' then 1 else 0)) a) b
  simp only [channel_apply, mul_mul_conjTranspose_apply] at hab
  rwa [sum_matrixUnit, sum_matrixUnit] at hab

/-- The rotation's entry at output `1`, input `0`, is `4/5`. -/
private theorem rotationThreeFifths_one_zero :
    rotationThreeFifths (fun _ => 1) 0 = 4 / 5 := by
  unfold rotationThreeFifths
  rw [if_neg (fun h => one_ne_zero (congrFun h 0)), if_pos (Pi.zero_apply 0)]

/-- The rotation's entry at output `0`, input `0`, is `3/5`. -/
private theorem rotationThreeFifths_zero_zero : rotationThreeFifths 0 0 = 3 / 5 := by
  unfold rotationThreeFifths
  rw [if_pos rfl]

/-- **The rank-one sum.** If a protocol's channel is the rotation's, the differences
`z_e = V((1, ∅), e) 0 − V((0, ∅), e) 0` of its dilation's entries have
`Σ_e z_e · conj z_e = (4/5 − 3/5)² = 1/25`. Each Kraus operator is `c_e·R`, so `z_e = c_e/5`; the
sum is read off the Gram data directly, without first proving that form. -/
private theorem sum_mul_conj_eq_of_channel_eq_rotation {m k u : ℕ} (p : Protocol m 1 k)
    (σ : Fin k ≃ Fin (0 + u))
    (h : channel p σ = fun ρ a b => (rotationThreeFifths * ρ * rotationThreeFifthsᴴ) a.1 b.1) :
    ∑ e : Fin u → ZMod 2,
        (dilation p σ (((fun _ => 1), 0), e) 0 - dilation p σ ((0, 0), e) 0)
          * starRingEnd ℂ (dilation p σ (((fun _ => 1), 0), e) 0 - dilation p σ ((0, 0), e) 0)
      = 1 / 25 := by
  have hG := choiGram_of_channel_eq_rotation p σ h
  have h11 := hG 0 ((fun _ => 1), 0) 0 ((fun _ => 1), 0)
  have h10 := hG 0 ((fun _ => 1), 0) 0 (0, 0)
  have h01 := hG 0 (0, 0) 0 ((fun _ => 1), 0)
  have h00 := hG 0 (0, 0) 0 (0, 0)
  unfold choiGram at h11 h10 h01 h00
  simp only [map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [h11, h10, h01, h00]
  simp only [rotationThreeFifths_one_zero, rotationThreeFifths_zero_zero, map_div₀,
    map_ofNat]
  norm_num

/-- **Outside the tower.** A map on matrices none of whose dilations, times any scalar of modulus
one, takes every value in `dyadicCyclotomicRing` is the channel of no protocol at any precision
`m ≥ 1`, read in any way: the contrapositive of the ring condition, through `isDilation_dilation`
and `choi_mem_dyadic` with `amp_choi`. Proved at T49.3.2. -/
theorem channel_ne_of_forall_dilation {m n k r u : ℕ}
    (Φ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ →
      Matrix ((Fin n → ZMod 2) × (Fin r → ZMod 2)) ((Fin n → ZMod 2) × (Fin r → ZMod 2)) ℂ)
    (hΦ : ∀ (e : ℕ)
      (D : Matrix (((Fin n → ZMod 2) × (Fin r → ZMod 2)) × (Fin e → ZMod 2)) (Fin n → ZMod 2) ℂ),
      IsDilation Φ D → ∀ z : ℂ, ‖z‖ = 1 → ∃ a x, z * D a x ∉ dyadicCyclotomicRing)
    (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u)) (hm : 1 ≤ m) :
    channel p σ ≠ Φ := by
  intro h
  have hD : IsDilation Φ (dilation p σ) := h ▸ isDilation_dilation p σ
  obtain ⟨a, x, hax⟩ := hΦ u (dilation p σ) hD 1 norm_one
  rw [one_mul] at hax
  exact hax (dilation_mem_dyadicCyclotomicRing p σ hm a x)

/-- **The rotation with cosine `3/5` is no protocol's channel**, at any precision `m ≥ 1` and with
any number of unread outcome bits and none read. Every Kraus operator of a dilation of a unitary
channel is a multiple `e·R`, so `e/5` is in the ring, and the squared moduli summing to `1` put
`1/5` in it, against `intCast_div_five_not_mem_dyadicCyclotomicRing`. Its Choi state is still a
carrier state at precision `1`: carrier-ness does not separate the tower. Proved at T49.3.2. -/
theorem rotation_not_realised {m k u : ℕ} (p : Protocol m 1 k) (σ : Fin k ≃ Fin (0 + u))
    (hm : 1 ≤ m) :
    channel p σ ≠ fun ρ a b => (rotationThreeFifths * ρ * rotationThreeFifthsᴴ) a.1 b.1 := by
  intro h
  have hz : ∀ e : Fin u → ZMod 2,
      dilation p σ (((fun _ => 1), 0), e) 0 - dilation p σ ((0, 0), e) 0 ∈ dyadicCyclotomicRing :=
    fun e => Subring.sub_mem _ (dilation_mem_dyadicCyclotomicRing p σ hm _ _)
      (dilation_mem_dyadicCyclotomicRing p σ hm _ _)
  have hsum := Subring.sum_mem dyadicCyclotomicRing (t := Finset.univ) fun e _ =>
    Subring.mul_mem _ (hz e) (starRingEnd_mem_dyadicCyclotomicRing (hz e))
  rw [sum_mul_conj_eq_of_channel_eq_rotation p σ h] at hsum
  have hfive : ((1 : ℤ) : ℂ) / 5 = ((5 : ℤ) : ℂ) * (1 / 25) := by
    push_cast
    norm_num
  exact intCast_div_five_not_mem_dyadicCyclotomicRing (a := 1) (by norm_num)
    (hfive ▸ Subring.mul_mem _ (intCast_mem _ 5) hsum)

end FTQCLib.Frame.Walkthrough

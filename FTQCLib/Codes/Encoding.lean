/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.PauliError
import FTQCLib.Carrier.Doubling
import FTQCLib.Stabilizer.Dimension
import FTQCLib.Stabilizer.Normalizer
import FTQCLib.Stabilizer.SignedLagrangian
import FTQCLib.Hierarchy.FrameExponent
import FTQCLib.Examples.CliffordFloorGeneration
import FTQCLib.Stabilizer.WittBasis

/-!
# Encoding into a signed stabilizer code

A **stabilizer code** here is signed (`StabCode n r`, `docs/TARGETS.md`, T29): `r` generators in
`SignedPauli n`, pairwise commuting, whose `pauli` parts are linearly independent over `𝔽₂`. So
`−1` is not in the group they generate and the code encodes `n − r` qubits. Their span `L`
(`StabCode.L`) is isotropic (`StabCode.isStabilizer_L`), so `r ≤ n` (`StabCode.r_le`), and they
determine a `FrameSignedStab n` (`StabCode.frame`): its Lagrangian is `L` and its sign `chi` at
`p ∈ L` is the phase of the ordered product, in `PauliGroup n`, of the generators the coordinates
of `p` select (`StabCode.frameChi`), so `2·sign` on each generator (`StabCode.frame_chi_gen`)
extended by the twisted law (`StabCode.frameChi_valid`); off `L` it is `0`, a choice no theorem
reads. A **code state** is an amplitude function fixed by every generator with its sign,
`g.act f = f` (`StabCode.IsCodeState`); `StabilizedBy` chooses a sign for each element and so
fixes none.

**Encoders.** The logical bits are the first `n − r` (`StabCode.logicalBit`) and the ancillas the
last `r` (`StabCode.ancillaBit`). An **encoder** (`StabCode.IsEncoder C w`) is a T05 gate word whose
letters are Clifford (`GateLetter.IsClifford`) and whose referee carries the `Z` of the `j`-th
ancilla to the `j`-th generator, sign included, and the `X` and the `Z` of each logical bit to
logical Paulis, Paulis with their sign in the normalizer of `L`: in each case `U p = P U` on every
amplitude function, `U` the word's referee (`CarriesPauli`). Every code has one at every precision
of at least `2` (`encoder_exists`). The encoder runs on `pinZeros r S`, the input with `r` free
bits appended and held at zero by T12's `pinZero`, the logical bits first (`StabCode.encodeInput`,
`StabCode.encode`); `zeroState` of `FrameCategory.lean` is the zero amplitude and is not this.

**What every encoder gives**, on a carrier state `S` at the word's precision, at any height:
the encoding is a carrier state whose amplitude is the referee on `S`'s amplitude padded with
zeros (`isCarrier_encode`); its amplitude is a code state (`encode_isCodeState`); a floor encodes
to a state `StateEq` to a floor whose Lagrangian contains `L` (`encode_floor`). A **logical
representative** of a bare Pauli `P` on the input is a Pauli on the register that differs by an
element of `L` from the one the encoder carries `P ⊗ I` to (`StabCode.IsLogicalRep`). Applied by
T64's `applyPauli`, it acts on every encoding as `P` on the input up to one sign that the
representative fixes, and some representative with its sign acts exactly as `P`
(`encode_logical`).

**Registers of blocks.** A register of `b` blocks (`Register b`) holds a code in each block and
lays out the blocks' bits one block after another (`Register.bit`), the logical input likewise.
Its input is the logical input with all the ancillas appended by `pinZeros` and moved into their
blocks by one fixed reindexing (`Register.layout`, `Register.input`); the blockwise word is each
block's word renamed into its block by an injective bit map (`GateLetter.renameBits`) and the
words concatenated (`Register.word`, `Register.blockEncode`). On a product input, the blocks'
inputs appended by T46's `appendState` (`appendStates`), the blockwise encoding is `StateEq` to the
blocks' encodings appended (`blockEncode_appendState`).

Everything here is frame-pure: no `FTQCLib.Hilbert` module is imported.

## Main definitions

* `StabCode`, `StabCode.L`, `StabCode.frameChi`, `StabCode.frame`, `StabCode.IsCodeState` — the
  signed code, its span, its sign, its `FrameSignedStab`, its code states.
* `pinZeros` — `r` free bits appended and held at zero.
* `GateLetter.IsClifford`, `CarriesPauli`, `StabCode.IsEncoder` — Clifford letters, what a word
  carries a Pauli to, the encoder property.
* `StabCode.encodeInput`, `StabCode.encode` — the input `S ⊗ |0…0⟩` and its run.
* `padPauli`, `StabCode.IsLogicalRep` — a Pauli on the input as one on the register, and the
  logical representatives of it.
* `GateLetter.renameBits` — a letter moved along an injective bit map.
* `appendStates`, `Register`, `Register.layout`, `Register.input`, `Register.word`,
  `Register.blockEncode` — states appended in order, the register of blocks, its input and its
  blockwise encoder.

## Main results

* `StabCode.isStabilizer_L`, `StabCode.r_le`, `StabCode.frameChi_valid`, `StabCode.frame_chi_gen`
  — the span is isotropic, `r ≤ n`, the sign obeys the twisted law and is `2·sign` on generators.
* `encoder_exists` — every code has an encoder at every precision of at least `2`.
* `isCarrier_encode`, `encode_isCodeState`, `encode_floor`, `encode_logical` — what every encoder
  does.
* `secondHalfLetter_eq_renameBits` — `Doubling.lean`'s second-half letter is a renaming.
* `blockEncode_appendState` — the blockwise encoder on a product input.

## Implementation notes

* **Precision.** A T05 run computes its referee only at the word's precision (`amp_run`), so the
  theorems take `S.m = m`; an input at a lower precision is first lifted by R7. `applyPauli` works
  at precision `2` where its Pauli has an odd number of Y; `encode_logical` is stated on
  amplitudes, which do not see the precision.
* **Height.** "At its own height" is read as: the encoder runs on a carrier state of any height.
  The encoding's height can be larger (H by the free rule adds a bound bit), so no theorem claims
  the height is kept, and `encode_floor` gives a floor up to `StateEq`, not the run itself.
* **`r ≤ n`.** The ancillas are the last `r` of `n` bits, so `n − r + r = n` is needed to read the
  appended input on `n` bits; it holds because an isotropic subspace has dimension at most `n`,
  and `StabCode.r_le` is proved here so that no definition's value holds `sorry`.
* **The sign off `L`** is `0`. `FrameSignedStab.valid` speaks only on `L`, and the fidelity note's
  condition 3 forbids relying on the value there.
* **The register's order.** Bits are block-major by `finSigmaFinEquiv`, block `0` first, and
  `appendStates` appends in the same order, the last block last.

## References

* D. Gottesman, *Stabilizer codes and quantum error correction*, arXiv:quant-ph/9705052: the
  stabilizer and its code space, the encoder `X_i ↦ X̄_i`, `Z_i ↦ Z̄_i`, `Z_{k+j} ↦ M_j`, its
  existence for any code, `UMU†` fixing `U|ψ⟩`, the encoded Paulis `N(S)/S`, and several blocks
  of one code; cited unit by unit above the declarations that restate them. The signed generators
  with independent Pauli parts, the frame's chart, the register's layout and the statements on
  carrier states are the frame's own (`docs/fidelity/T29.md`).
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer FTQCLib.Cohomology

variable {n r : ℕ}

/-! ## The signed code -/

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:ha651a9afb466
-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:he4985923b04d
/-- **A signed stabilizer code** on `n` qubits with `r` generators: each a Pauli with its sign,
pairwise commuting, their `pauli` parts linearly independent over `𝔽₂`. The source's stabilizer
is an Abelian subgroup of the Pauli group without `−1`; generators with independent Pauli parts
are a minimal generating set of such a group, and independence is what excludes `−1`. -/
structure StabCode (n r : ℕ) where
  /-- The `j`-th generator, a Pauli with its sign. -/
  gen : Fin r → SignedPauli n
  /-- The generators pairwise commute. -/
  commute : ∀ i j, omega (gen i).pauli (gen j).pauli = 0
  /-- The generators' Pauli parts are linearly independent. -/
  independent : LinearIndependent (ZMod 2) fun j => (gen j).pauli

namespace StabCode

/-- The span of the generators' Pauli parts, the code's stabilizer without signs. -/
def L (C : StabCode n r) : Submodule (ZMod 2) (Pauli n) :=
  Submodule.span (ZMod 2) (Set.range fun j => (C.gen j).pauli)

/-- **The span is isotropic**: the generators commute and `omega` is bilinear. -/
theorem isStabilizer_L (C : StabCode n r) : IsStabilizer C.L := by
  have hgen : ∀ i, ∀ q ∈ C.L, omega (C.gen i).pauli q = 0 := by
    intro i q hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact C.commute i j
    | zero => exact omega_zero_right _
    | add y z _ _ ihy ihz => rw [omega_add_right, ihy, ihz, add_zero]
    | smul a y _ ihy => rw [omega_smul_right, ihy, mul_zero]
  intro p hp q hq
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hgen i q hq
  | zero => exact omega_zero_left q
  | add x y _ _ ihx ihy => rw [omega_add_left, ihx, ihy, add_zero]
  | smul a x _ ihx => rw [omega_smul_left, ihx, mul_zero]

/-- **At most `n` generators**: the span has dimension `r` and is isotropic. -/
theorem r_le (C : StabCode n r) : r ≤ n := by
  have h := finrank_le_of_isStabilizer C.isStabilizer_L
  rwa [L, finrank_span_eq_card C.independent, Fintype.card_fin] at h

/-- The ordered product in `PauliGroup n`, generator `0` first, of the generators whose
coordinate in `c` is `1`. -/
noncomputable def product (C : StabCode n r) (c : Fin r →₀ ZMod 2) : PauliGroup n :=
  ((List.finRange r).map fun j => (C.gen j).toPauliGroup ^ (c j).val).prod

open Classical in
/-- **The code's sign**: at `p ∈ L`, the phase of the product of the generators that `p`'s
coordinates select, which is `p` with the sign the generators' signs give it; `0` off `L`. -/
noncomputable def frameChi (C : StabCode n r) (p : Pauli n) : ZMod 4 :=
  if hp : p ∈ C.L then (C.product (C.independent.repr ⟨p, hp⟩)).phase else 0

/-- The sign of the identity is `0`: its coordinates are zero and the empty product is `1`. -/
theorem frameChi_zero (C : StabCode n r) : C.frameChi 0 = 0 := by
  have h0 : C.independent.repr ⟨0, C.L.zero_mem⟩ = 0 := map_zero _
  unfold frameChi
  rw [dif_pos C.L.zero_mem, h0]
  simp [product]

/-- A Pauli with its sign squares to the identity in the Pauli group: the phase is
`4·sign + betaFrame p p = 0` and the base `p + p = 0`. -/
private theorem toPauliGroup_mul_self (P : SignedPauli n) :
    P.toPauliGroup * P.toPauliGroup = 1 := by
  have h4 : ∀ y : ZMod 4, 2 * y + 2 * y = 0 := by decide
  refine PauliGroup.ext ?_ ?_
  · rw [PauliGroup.mul_phase, PauliGroup.one_phase]
    change 2 * ((P.sign.val : ℕ) : ZMod 4) + 2 * ((P.sign.val : ℕ) : ZMod 4)
      + betaFrame P.pauli P.pauli = 0
    rw [betaFrame_self, add_zero]
    exact h4 _
  · rw [PauliGroup.mul_base, PauliGroup.one_base]
    exact pauli_add_self P.pauli

/-- Two generators commute in the Pauli group: `betaFrame` is symmetric where `omega` vanishes. -/
private theorem gen_commute (C : StabCode n r) (i j : Fin r) :
    Commute (C.gen i).toPauliGroup (C.gen j).toPauliGroup := by
  change _ * _ = _ * _
  refine PauliGroup.ext ?_ ?_
  · rw [PauliGroup.mul_phase, PauliGroup.mul_phase]
    change 2 * (((C.gen i).sign.val : ℕ) : ZMod 4) + 2 * (((C.gen j).sign.val : ℕ) : ZMod 4)
        + betaFrame (C.gen i).pauli (C.gen j).pauli
      = 2 * (((C.gen j).sign.val : ℕ) : ZMod 4) + 2 * (((C.gen i).sign.val : ℕ) : ZMod 4)
        + betaFrame (C.gen j).pauli (C.gen i).pauli
    rw [betaFrame_swap (C.gen i).pauli (C.gen j).pauli, C.commute i j, ZMod.val_zero,
      Nat.cast_zero, mul_zero, add_zero]
    ring
  · rw [PauliGroup.mul_base, PauliGroup.mul_base]
    exact add_comm _ _

/-- An involution's power at a sum of bits is the product of its powers. -/
private theorem pow_val_add {G : Type*} [Monoid G] {x : G} (hx : x * x = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  exact (pow_eq_pow_mod _ (by rw [pow_two]; exact hx)).symm

/-- **The ordered product is additive in the exponents** for pairwise commuting involutions. -/
private theorem prod_map_pow_add {G : Type*} [Monoid G] {x : Fin r → G}
    (hsq : ∀ j, x j * x j = 1) (hc : ∀ i j, Commute (x i) (x j)) (c c' : Fin r → ZMod 2)
    (l : List (Fin r)) :
    (l.map fun j => x j ^ (c j + c' j).val).prod
      = (l.map fun j => x j ^ (c j).val).prod * (l.map fun j => x j ^ (c' j).val).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, mul_one]
  | cons j l ih =>
    have hcomm : Commute (x j ^ (c' j).val) (l.map fun k => x k ^ (c k).val).prod :=
      Commute.list_prod_right _ _ fun y hy => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
        exact ((hc j k).pow_left _).pow_right _
    rw [List.map_cons, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.prod_cons, ih, pow_val_add (hsq j)]
    simp only [mul_assoc]
    rw [← mul_assoc (x j ^ (c' j).val), hcomm.eq, mul_assoc]

/-- The base of a power is the multiple of the base. -/
private theorem base_pow (x : PauliGroup n) (k : ℕ) : (x ^ k).base = k • x.base := by
  induction k with
  | zero => rw [pow_zero, zero_nsmul, PauliGroup.one_base]
  | succ k ih => rw [pow_succ, PauliGroup.mul_base, ih, succ_nsmul]

/-- The base of an ordered product of powers is the sum of the multiples of the bases. -/
private theorem base_prod_map_pow (x : Fin r → PauliGroup n) (k : Fin r → ℕ) (l : List (Fin r)) :
    (l.map fun j => x j ^ k j).prod.base = (l.map fun j => k j • (x j).base).sum := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons, PauliGroup.mul_base, ih,
      base_pow]

/-- The base of the product the coordinates `c` select is the combination of the generators. -/
private theorem product_base (C : StabCode n r) (c : Fin r →₀ ZMod 2) :
    (C.product c).base = ∑ j, c j • (C.gen j).pauli := by
  refine (base_prod_map_pow (fun j => (C.gen j).toPauliGroup) (fun j => (c j).val)
    (List.finRange r)).trans ?_
  rw [Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  change (c j).val • (C.gen j).pauli = c j • (C.gen j).pauli
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]

/-- The combination of the generators by the coordinates of `p ∈ L` is `p`. -/
private theorem sum_repr (C : StabCode n r) {p : Pauli n} (hp : p ∈ C.L) :
    ∑ j, C.independent.repr ⟨p, hp⟩ j • (C.gen j).pauli = p := by
  have h := C.independent.linearCombination_repr ⟨p, hp⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at h
  · exact h
  · exact fun _ => zero_smul _ _

/-- The product is multiplicative in the coordinates. -/
private theorem product_add (C : StabCode n r) (c c' : Fin r →₀ ZMod 2) :
    C.product (c + c') = C.product c * C.product c' :=
  prod_map_pow_add (x := fun j => (C.gen j).toPauliGroup)
    (fun j => toPauliGroup_mul_self (C.gen j)) (gen_commute C) (⇑c) (⇑c') (List.finRange r)

/-- The twisted law, from the product's multiplicativity and the phase of a product. -/
private theorem frameChi_add (C : StabCode n r) {p q : Pauli n} (hp : p ∈ C.L) (hq : q ∈ C.L) :
    C.frameChi (p + q) = C.frameChi p + C.frameChi q + betaFrame p q := by
  have hpq : p + q ∈ C.L := C.L.add_mem hp hq
  have hrepr : C.independent.repr ⟨p + q, hpq⟩
      = C.independent.repr ⟨p, hp⟩ + C.independent.repr ⟨q, hq⟩ :=
    map_add C.independent.repr ⟨p, hp⟩ ⟨q, hq⟩
  unfold frameChi
  rw [dif_pos hpq, dif_pos hp, dif_pos hq, hrepr, product_add, PauliGroup.mul_phase,
    product_base, product_base, sum_repr C hp, sum_repr C hq]

/-- **The twisted law on `L`**: the product of the generators selected by the coordinates of
`p + q` is the product for `p` times the product for `q`, since the generators commute and square
to `1`, and the phase of a product is the phases' sum plus `betaFrame`. -/
theorem frameChi_valid (C : StabCode n r) :
    ∀ p ∈ C.L, ∀ q ∈ C.L, C.frameChi (p + q) = C.frameChi p + C.frameChi q + betaFrame p q :=
  fun _ hp _ hq => frameChi_add C hp hq

/-- **The code's `FrameSignedStab`**: Lagrangian the span `L`, sign `frameChi`. -/
noncomputable def frame (C : StabCode n r) : FrameSignedStab n where
  L := C.L
  chi := C.frameChi
  chi_zero := C.frameChi_zero
  valid := C.frameChi_valid

/-- The frame's Lagrangian is the span of the generators. -/
theorem frame_L (C : StabCode n r) : C.frame.L = C.L := rfl

/-- **The frame's sign on a generator is `2·sign`**, the power of `i` that is `(−1)^sign`. -/
theorem frame_chi_gen (C : StabCode n r) (i : Fin r) :
    C.frame.chi (C.gen i).pauli = 2 * ((C.gen i).sign.val : ZMod 4) := by
  have hi : (C.gen i).pauli ∈ C.L := Submodule.subset_span ⟨i, rfl⟩
  change C.frameChi _ = _
  unfold frameChi
  rw [dif_pos hi, C.independent.repr_eq_single i ⟨_, hi⟩ rfl, product,
    List.prod_map_eq_pow_single i _ (fun j hj _ => by
      rw [Finsupp.single_apply, if_neg (Ne.symm hj), ZMod.val_zero, pow_zero]),
    List.count_eq_one_of_mem (List.nodup_finRange r) (List.mem_finRange i),
    Finsupp.single_eq_same, pow_one]
  exact congrArg PauliGroup.phase (pow_one (C.gen i).toPauliGroup)

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:ha651a9afb466
/-- **A code state**: an amplitude function fixed by every generator with its sign. Fixed by the
generators, it is fixed by the group they generate, the source's code space; the zero function is
one. -/
def IsCodeState (C : StabCode n r) (f : (Fin n → ZMod 2) → ℂ) : Prop :=
  ∀ j, (C.gen j).act f = f

/-- The `i`-th logical bit, among the first `n − r`. -/
def logicalBit (_C : StabCode n r) (i : Fin (n - r)) : Fin n :=
  Fin.castLE (Nat.sub_le n r) i

/-- The `j`-th ancilla, among the last `r` bits. -/
def ancillaBit (C : StabCode n r) (j : Fin r) : Fin n :=
  Fin.cast (Nat.sub_add_cancel C.r_le) (Fin.natAdd (n - r) j)

end StabCode

/-! ## Ancillas held at zero -/

/-- **`r` free bits appended and held at zero**, `S ⊗ |0…0⟩`: `r` uses of T12's `pinZero`, each
adding one last bit, so `S`'s bits come first and the zeros last. -/
noncomputable def pinZeros {N : ℕ} : (r : ℕ) → KernelSumState N → KernelSumState (N + r)
  | 0, S => S
  | r + 1, S => pinZero (pinZeros r S)

/-! ## Encoders -/

/-- **A Clifford letter**: H and CNOT, and a diagonal letter whose exponent has extended level at
most two, the check `NormalGate.WF` makes in `CliffordWordFloor.lean`. -/
def GateLetter.IsClifford {m : ℕ} : GateLetter n m → Prop
  | .hadamard _ => True
  | .diagonal D => levelExt D ≤ 2
  | .cnot _ _ _ => True

/-- **The word carries the Hermitian Pauli `p` to `P`**: `U p = P U` on every amplitude function,
`U` the word's referee; with `U` invertible, `U p U⁻¹ = P`. -/
def CarriesPauli {m : ℕ} (w : GateWord n m) (p : Pauli n) (P : SignedPauli n) : Prop :=
  ∀ f, runAmp w (pauliAct p f) = P.act (runAmp w f)

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:hba0d3b4e9157
/-- **An encoder of the code**: a gate word of Clifford letters that carries the `Z` of the `j`-th
ancilla to the `j`-th generator, sign included, and the `X` and the `Z` of each logical bit to
logical Paulis, Paulis with their sign in the normalizer of `L`. The source's encoder, with the
data first and the ancillas last; the images of the ancillas' `X` are left free, as there. -/
structure StabCode.IsEncoder (C : StabCode n r) {m : ℕ} (w : GateWord n m) : Prop where
  /-- Every letter is Clifford. -/
  clifford : ∀ g ∈ w, g.IsClifford
  /-- The `Z` of the `j`-th ancilla goes to the `j`-th generator. -/
  ancilla : ∀ j : Fin r, CarriesPauli w (pauliz (C.ancillaBit j)) (C.gen j)
  /-- The `X` of each logical bit goes to a logical Pauli. -/
  logicalX : ∀ i : Fin (n - r),
    ∃ P : SignedPauli n, P.pauli ∈ normalizer C.L ∧ CarriesPauli w (paulix (C.logicalBit i)) P
  /-- The `Z` of each logical bit goes to a logical Pauli. -/
  logicalZ : ∀ i : Fin (n - r),
    ∃ P : SignedPauli n, P.pauli ∈ normalizer C.L ∧ CarriesPauli w (pauliz (C.logicalBit i)) P

namespace StabCode

/-- **The encoder's input**, `S ⊗ |0…0⟩`: `pinZeros r S`, read on `n = (n − r) + r` bits. -/
noncomputable def encodeInput (C : StabCode n r) (S : KernelSumState (n - r)) : KernelSumState n :=
  castBits (Nat.sub_add_cancel C.r_le) (pinZeros r S)

/-- **The encoding** of `S` by the word `w`: T05's run of `w` on the encoder's input. -/
noncomputable def encode (C : StabCode n r) {m : ℕ} (w : GateWord n m)
    (S : KernelSumState (n - r)) : KernelSumState n :=
  run w (C.encodeInput S)

end StabCode

/-! ## The symplectic lift

The linear algebra of the existence proof: the generators' Pauli parts extend to a symplectic
basis of `Pauli n` (destabilizers by duality, the rest by Witt's theorem on the orthogonal
complement, `exists_symplecticBasis_of_nondeg_alt`), and a symplectic basis is the image of the
standard one under a symplectic map. -/

section SymplecticLift

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- In a symplectic pair the coefficients of a combination are read off by pairing: that of `e i`
against `f i`, that of `f i` against `e i`. -/
private theorem coeff_symplecticPair {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2} {e f : ι → V} (h : IsSymplecticPair B e f)
    (c : ι ⊕ ι → ZMod 2) (i : ι) :
    B (∑ s, c s • Sum.elim e f s) (f i) = c (Sum.inl i)
      ∧ B (e i) (∑ s, c s • Sum.elim e f s) = c (Sum.inr i) := by
  constructor
  · rw [map_sum, LinearMap.sum_apply, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, map_smul, LinearMap.smul_apply, smul_eq_mul,
      h.pairing, h.f_isOrtho, mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [map_sum, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, map_smul, smul_eq_mul, h.pairing, h.e_isOrtho,
      mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]

/-- A symplectic pair is linearly independent. -/
private theorem linearIndependent_symplecticPair {ι : Type*} [Finite ι] [DecidableEq ι]
    {B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2} {e f : ι → V} (h : IsSymplecticPair B e f) :
    LinearIndependent (ZMod 2) (Sum.elim e f) := by
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  rcases s with i | i
  · rw [← (coeff_symplecticPair h c i).1, hc, map_zero, LinearMap.zero_apply]
  · rw [← (coeff_symplecticPair h c i).2, hc, map_zero]

/-- A symplectic pair stays one along a bijection of its indices. -/
private theorem isSymplecticPair_comp {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2} {e f : ι → V} (h : IsSymplecticPair B e f)
    (σ : κ ≃ ι) : IsSymplecticPair B (e ∘ σ) (f ∘ σ) where
  pairing i j := by
    rw [Function.comp_apply, Function.comp_apply, h.pairing]
    by_cases hij : i = j
    · rw [if_pos (congrArg σ hij), if_pos hij]
    · rw [if_neg (σ.injective.ne hij), if_neg hij]
  e_isOrtho i j := h.e_isOrtho (σ i) (σ j)
  f_isOrtho i j := h.f_isOrtho (σ i) (σ j)

/-- Two symplectic pairs of an alternating form have the same Gram matrix. -/
private theorem gram_symplecticPair {ι : Type*} [DecidableEq ι]
    {B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2} (hA : B.IsAlt) {e f e' f' : ι → V}
    (h : IsSymplecticPair B e f) (h' : IsSymplecticPair B e' f') (s t : ι ⊕ ι) :
    B (Sum.elim e f s) (Sum.elim e f t) = B (Sum.elim e' f' s) (Sum.elim e' f' t) := by
  rcases s with i | i <;> rcases t with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · rw [h.e_isOrtho, h'.e_isOrtho]
  · rw [h.pairing, h'.pairing]
  · rw [BilinForm_alt_symm B hA (e j) (f i), BilinForm_alt_symm B hA (e' j) (f' i), h.pairing,
      h'.pairing]
  · rw [h.f_isOrtho, h'.f_isOrtho]

end SymplecticLift

/-- A symplectic pair of size `n` in `Pauli n` is a basis: independent, and `2n` vectors. -/
private noncomputable def pairBasis {e f : Fin n → Pauli n}
    (h : IsSymplecticPair (omegaBilin (n := n)) e f) :
    Module.Basis (Fin n ⊕ Fin n) (ZMod 2) (Pauli n) :=
  Module.Basis.mk (linearIndependent_symplecticPair h) (Submodule.eq_top_of_finrank_eq (by
    rw [finrank_span_eq_card (linearIndependent_symplecticPair h), Fintype.card_sum,
      Fintype.card_fin, finrank_Pauli]
    ring)).ge

/-- **A symplectic pair of size `n` is the image of the standard pair under a symplectic map**:
the map sending one basis to the other keeps `omega`, as the two Gram matrices agree. -/
private theorem exists_isClifford_of_isSymplecticPair {e f : Fin n → Pauli n}
    (h : IsSymplecticPair (omegaBilin (n := n)) e f) :
    ∃ T : Pauli n ≃ₗ[ZMod 2] Pauli n, Gates.IsClifford T ∧
      ∀ i, T (paulix i) = e i ∧ T (pauliz i) = f i := by
  let bstd := pairBasis (isSymplecticPair_omegaBilin (n := n))
  let bnew := pairBasis h
  have hT : ∀ s, bstd.equiv bnew (Equiv.refl _) (Sum.elim paulix pauliz s) = Sum.elim e f s := by
    intro s
    have h1 : bstd s = Sum.elim paulix pauliz s := Module.Basis.mk_apply _ _ _
    have h2 : bnew s = Sum.elim e f s := Module.Basis.mk_apply _ _ _
    rw [← h1, Module.Basis.equiv_apply, Equiv.refl_apply, h2]
  refine ⟨bstd.equiv bnew (Equiv.refl _), fun x y => ?_,
    fun i => ⟨hT (Sum.inl i), hT (Sum.inr i)⟩⟩
  have hform : (omegaBilin (n := n)).compl₁₂
      (bstd.equiv bnew (Equiv.refl _) : Pauli n →ₗ[ZMod 2] Pauli n)
      (bstd.equiv bnew (Equiv.refl _) : Pauli n →ₗ[ZMod 2] Pauli n) = omegaBilin := by
    refine LinearMap.ext_basis bstd bstd fun s t => ?_
    have h1 : ∀ s, bstd s = Sum.elim paulix pauliz s := fun s => Module.Basis.mk_apply _ _ _
    rw [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, h1, h1, hT, hT]
    exact gram_symplecticPair Gates.omegaBilin_isAlt h isSymplecticPair_omegaBilin s t
  exact LinearMap.congr_fun₂ hform x y

/-- Membership in a normalizer is commuting with every element. -/
private theorem mem_normalizer_iff {S : Submodule (ZMod 2) (Pauli n)} {v : Pauli n} :
    v ∈ normalizer S ↔ ∀ q ∈ S, omega v q = 0 :=
  Iff.rfl

/-- Commuting with a spanning family is commuting with the span. -/
private theorem mem_normalizer_span {ι : Type*} {g : ι → Pauli n} {v : Pauli n}
    (hv : ∀ j, omega v (g j) = 0) :
    v ∈ normalizer (Submodule.span (ZMod 2) (Set.range g)) := by
  have hle : Submodule.span (ZMod 2) (Set.range g) ≤ LinearMap.ker (omegaBilin v) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact LinearMap.mem_ker.mpr (hv j)
  exact mem_normalizer_iff.mpr fun q hq => LinearMap.mem_ker.mp (hle hq)

/-- **A dual family**: independent `g` have `d` with `ω(d i, g j) = δ_{ij}`, since the map
`v ↦ (ω(v, g j))_j` has the normalizer as kernel, of dimension `2n − r`, so it is onto. -/
private theorem exists_dual_family {g : Fin r → Pauli n} (hli : LinearIndependent (ZMod 2) g) :
    ∃ d : Fin r → Pauli n, ∀ i j, omega (d i) (g j) = if i = j then 1 else 0 := by
  let Φ : Pauli n →ₗ[ZMod 2] (Fin r → ZMod 2) :=
    LinearMap.pi fun j => (omegaBilin (n := n)).flip (g j)
  have hker : LinearMap.ker Φ = normalizer (Submodule.span (ZMod 2) (Set.range g)) := by
    ext v
    rw [LinearMap.mem_ker]
    constructor
    · intro hv
      exact mem_normalizer_span fun j => congrFun hv j
    · intro hv
      funext j
      exact mem_normalizer_iff.mp hv (g j) (Submodule.subset_span ⟨j, rfl⟩)
  have hspan := finrank_span_eq_card hli
  rw [Fintype.card_fin] at hspan
  have hrank := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hker, finrank_normalizer, hspan, finrank_Pauli] at hrank
  have hr : r ≤ 2 * n := by
    have h := Submodule.finrank_le (Submodule.span (ZMod 2) (Set.range g))
    rwa [hspan, finrank_Pauli] at h
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    omega
  choose d hd using fun i => hsurj (Pi.single i 1)
  refine ⟨d, fun i j => ?_⟩
  have h := congrFun (hd i) j
  change omega (d i) (g j) = (Pi.single i (1 : ZMod 2) : Fin r → ZMod 2) j at h
  rw [h, Pi.single_apply]
  by_cases hij : i = j
  · rw [if_pos hij.symm, if_pos hij]
  · rw [if_neg (Ne.symm hij), if_neg hij]

/-- `omega` against a vector plus a combination, expanded. -/
private theorem omega_add_sum_left (a y : Pauli n) (c : Fin r → ZMod 2) (g : Fin r → Pauli n) :
    omega (a + ∑ k, c k • g k) y = omega a y + ∑ k, c k * omega (g k) y := by
  change omegaBilin (a + ∑ k, c k • g k) y = omegaBilin a y + ∑ k, c k * omegaBilin (g k) y
  rw [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- `omega` of a vector against a vector plus a combination, expanded. -/
private theorem omega_add_sum_right (y a : Pauli n) (c : Fin r → ZMod 2) (g : Fin r → Pauli n) :
    omega y (a + ∑ k, c k • g k) = omega y a + ∑ k, c k * omega y (g k) := by
  change omegaBilin y (a + ∑ k, c k • g k) = omegaBilin y a + ∑ k, c k * omegaBilin y (g k)
  rw [map_add, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- **Destabilizers**: a dual family corrected by multiples of the generators to be isotropic,
`d i + Σ_{k < i} ω(d i, d k) g k`, so `(d, g)` is a symplectic pair. -/
private theorem exists_destabilizers {g : Fin r → Pauli n} (hli : LinearIndependent (ZMod 2) g)
    (hiso : ∀ i j, omega (g i) (g j) = 0) :
    ∃ d : Fin r → Pauli n, IsSymplecticPair (omegaBilin (n := n)) d g := by
  obtain ⟨d, hd⟩ := exists_dual_family hli
  have hd' : ∀ k l, omega (g k) (d l) = if l = k then 1 else 0 := fun k l => by
    rw [omega_comm]
    exact hd l k
  let c : Fin r → Fin r → ZMod 2 := fun i k => if k < i then omega (d i) (d k) else 0
  have hdg : ∀ i j, omega (d i + ∑ k, c i k • g k) (g j) = if i = j then 1 else 0 := by
    intro i j
    rw [omega_add_sum_left, hd]
    simp only [hiso, mul_zero, Finset.sum_const_zero, add_zero]
  refine ⟨fun i => d i + ∑ k, c i k • g k, ⟨hdg, fun i l => ?_, hiso⟩⟩
  change omega (d i + ∑ k, c i k • g k) (d l + ∑ k, c l k • g k) = 0
  rw [omega_add_sum_right, omega_add_sum_left]
  simp only [hdg, hd', mul_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  rcases lt_trichotomy i l with hil | rfl | hil
  · simp only [c, if_pos hil, if_neg (not_lt.mpr hil.le), omega_comm (d l) (d i), add_zero]
    exact h2 _
  · simp only [c, lt_irrefl, if_false, omega_self, add_zero]
  · simp only [c, if_pos hil, if_neg (not_lt.mpr hil.le), add_zero]
    exact h2 _

/-- **The generators' Pauli parts extend to a symplectic basis** indexed by the logical bits and
the ancillas, the `Z`-images of the ancillas the generators: the destabilizers complete them to
`2r` vectors, and Witt's theorem gives a symplectic basis of their orthogonal complement, which
has dimension `2(n − r)`. -/
private theorem exists_symplecticPair_extending (hr : r ≤ n) {g : Fin r → Pauli n}
    (hli : LinearIndependent (ZMod 2) g) (hiso : ∀ i j, omega (g i) (g j) = 0) :
    ∃ e f : Fin (n - r) ⊕ Fin r → Pauli n,
      IsSymplecticPair (omegaBilin (n := n)) e f ∧ ∀ j, f (Sum.inr j) = g j := by
  obtain ⟨d, hdg⟩ := exists_destabilizers hli hiso
  let W0 : Submodule (ZMod 2) (Pauli n) := Submodule.span (ZMod 2) (Set.range (Sum.elim d g))
  let Wp : Submodule (ZMod 2) (Pauli n) :=
    LinearMap.BilinForm.orthogonal (omegaBilin (n := n)) W0
  have hW0 : Module.finrank (ZMod 2) W0 = 2 * r := by
    rw [finrank_span_eq_card (linearIndependent_symplecticPair hdg), Fintype.card_sum,
      Fintype.card_fin]
    ring
  have hWp : Module.finrank (ZMod 2) Wp = 2 * (n - r) := by
    rw [LinearMap.BilinForm.finrank_orthogonal omegaBilin_nondegenerate, finrank_Pauli, hW0]
    omega
  have hd0 : ∀ i, d i ∈ W0 := fun i => Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hg0 : ∀ i, g i ∈ W0 := fun i => Submodule.subset_span ⟨Sum.inr i, rfl⟩
  have hperp : ∀ w ∈ W0, ∀ x : Wp, omega w x = 0 := fun w hw x =>
    (LinearMap.BilinForm.mem_orthogonal_iff.mp x.2) w hw
  have hperp' : ∀ w ∈ W0, ∀ x : Wp, omega x w = 0 := fun w hw x => by
    rw [omega_comm]
    exact hperp w hw x
  have hdisj : Disjoint W0 Wp := by
    rw [Submodule.disjoint_def]
    intro v hv0 hvp
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hv0
    have hc : c = 0 := by
      funext s
      rcases s with i | i
      · rw [← (coeff_symplecticPair hdg c i).1]
        exact hperp' (g i) (hg0 i) ⟨_, hvp⟩
      · rw [← (coeff_symplecticPair hdg c i).2]
        exact hperp (d i) (hd0 i) ⟨_, hvp⟩
    rw [hc]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  have hN : (LinearMap.BilinForm.restrict (omegaBilin (n := n)) Wp).Nondegenerate :=
    nondegenerate_restrict_orthogonal_of_disjoint _ omegaBilin_nondegenerate
      Gates.omegaBilin_isAlt W0 hdisj
  have hA : (LinearMap.BilinForm.restrict (omegaBilin (n := n)) Wp).IsAlt :=
    fun x => Gates.omegaBilin_isAlt x.val
  obtain ⟨k, e', f', hk, hef, hee, hff⟩ := exists_symplecticBasis_of_nondeg_alt Wp _ hN hA
  obtain rfl : k = n - r := by omega
  refine ⟨Sum.elim (fun i => (e' i : Pauli n)) d, Sum.elim (fun i => (f' i : Pauli n)) g,
    ⟨fun s t => ?_, fun s t => ?_, fun s t => ?_⟩, fun j => rfl⟩
  · rcases s with i | i <;> rcases t with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false]
    · exact hef i j
    · exact hperp' (g j) (hg0 j) (e' i)
    · exact hperp (d i) (hd0 i) (f' j)
    · exact hdg.pairing i j
  · rcases s with i | i <;> rcases t with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact hee i j
    · exact hperp' (d j) (hd0 j) (e' i)
    · exact hperp (d i) (hd0 i) (e' j)
    · exact hdg.e_isOrtho i j
  · rcases s with i | i <;> rcases t with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact hff i j
    · exact hperp' (g j) (hg0 j) (f' i)
    · exact hperp (g i) (hg0 i) (f' j)
    · exact hdg.f_isOrtho i j

namespace StabCode

/-- The ancillas are distinct bits. -/
private theorem ancillaBit_injective (C : StabCode n r) : Function.Injective C.ancillaBit := by
  intro a b h
  have hv : (n - r) + a.val = (n - r) + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- **The symplectic lift of the code**: a symplectic map sending the `Z` of the `j`-th ancilla to
the `j`-th generator's Pauli part and the `X` and `Z` of each logical bit into the normalizer. -/
private theorem exists_clifford_lift (C : StabCode n r) :
    ∃ T : Pauli n ≃ₗ[ZMod 2] Pauli n, Gates.IsClifford T ∧
      (∀ j, T (pauliz (C.ancillaBit j)) = (C.gen j).pauli) ∧
      (∀ i, T (paulix (C.logicalBit i)) ∈ normalizer C.L) ∧
      ∀ i, T (pauliz (C.logicalBit i)) ∈ normalizer C.L := by
  obtain ⟨e, f, hef, hf⟩ := exists_symplecticPair_extending C.r_le C.independent C.commute
  let σ : Fin n ≃ Fin (n - r) ⊕ Fin r :=
    (finCongr (Nat.sub_add_cancel C.r_le).symm).trans finSumFinEquiv.symm
  obtain ⟨T, hT, hTe⟩ := exists_isClifford_of_isSymplecticPair (isSymplecticPair_comp hef σ)
  have hσa : ∀ j, σ (C.ancillaBit j) = Sum.inr j := fun j => by
    have h1 : finCongr (Nat.sub_add_cancel C.r_le).symm (C.ancillaBit j) = Fin.natAdd (n - r) j :=
      Fin.ext rfl
    rw [Equiv.trans_apply, h1, finSumFinEquiv_symm_apply_natAdd]
  have hσl : ∀ i, σ (C.logicalBit i) = Sum.inl i := fun i => by
    have h1 : finCongr (Nat.sub_add_cancel C.r_le).symm (C.logicalBit i) = Fin.castAdd r i :=
      Fin.ext rfl
    rw [Equiv.trans_apply, h1, finSumFinEquiv_symm_apply_castAdd]
  have hfj : ∀ j, f (Sum.inr j) = (C.gen j).pauli := hf
  refine ⟨T, hT, fun j => ?_, fun i => mem_normalizer_span fun j => ?_,
    fun i => mem_normalizer_span fun j => ?_⟩
  · rw [(hTe _).2, Function.comp_apply, hσa, hfj]
  · rw [(hTe _).1, Function.comp_apply, hσl, ← hfj j]
    exact (hef.pairing (Sum.inl i) (Sum.inr j)).trans (if_neg Sum.inl_ne_inr)
  · rw [(hTe _).2, Function.comp_apply, hσl, ← hfj j]
    exact hef.f_isOrtho (Sum.inl i) (Sum.inr j)

end StabCode

/-! ## Clifford words carry Paulis to Paulis

A well-formed word of `CliffordWordFloor.lean`'s alphabet, read as a T05 word, carries every
Pauli to its symplectic image times a scalar, letter by letter
(`pauliAct_pauliSwapOn_walshTransform`, `pauliAct_zShearBy_of_shift`, `pauliAct_cnotPauli`); the
scalar is a sign since both Paulis square to the identity and the referee is invertible. -/

/-- The referee of the zero function is zero. -/
private theorem runAmp_zero_fun {m : ℕ} (W : GateWord n m) : runAmp W 0 = 0 := by
  have h00 := runAmp_add_smul W 0 0 1
  rw [smul_zero, add_zero, one_smul] at h00
  exact left_eq_add.mp h00

/-- The referee commutes with a constant factor. -/
private theorem runAmp_mul_left {m : ℕ} (W : GateWord n m) (c : ℂ)
    (h : (Fin n → ZMod 2) → ℂ) : runAmp W (fun w => c * h w) = fun w => c * runAmp W h w := by
  have hc := runAmp_add_smul W 0 h c
  rw [zero_add, runAmp_zero_fun, zero_add] at hc
  exact hc

/-- **One well-formed letter**, as a T05 Clifford letter, carries every Pauli to its symplectic
image times a scalar. -/
private theorem exists_letter_intertwining {m : ℕ} (hm : 2 ≤ m) (g : NormalGate n m)
    (hg : g.WF) :
    ∃ G : GateLetter n m, G.IsClifford ∧ ∀ p : Pauli n, ∃ c : ℂ, ∀ f,
      letterAmp G (pauliAct p f) = fun w => c * pauliAct (letterLin g p) (letterAmp G f) w := by
  have hsq : ∀ k : ℕ, ((-1 : ℂ) ^ k) * ((-1) ^ k) = 1 := fun k => by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  cases g with
  | H k =>
    refine ⟨.hadamard k, trivial, fun p => ⟨(-1) ^ ((p.X k).val * (p.Z k).val), fun f => ?_⟩⟩
    funext w
    have key := congrFun (pauliAct_pauliSwapOn_walshTransform k p f) w
    change walshTransform k (pauliAct p f) w
      = (-1) ^ ((p.X k).val * (p.Z k).val) * pauliAct (pauliSwapOn {k} p) (walshTransform k f) w
    rw [key, ← mul_assoc, hsq, one_mul]
  | Diag D =>
    refine ⟨.diagonal D, hg, fun p => ?_⟩
    obtain ⟨c0, hc0⟩ := diagShiftDatumBy_polarMatrix D hg ⊤ p.X Submodule.mem_top
    obtain ⟨K, hK, hkey⟩ : ∃ K : ℂ, K ≠ 0 ∧ ∀ f : (Fin n → ZMod 2) → ℂ,
        pauliAct (letterLin (NormalGate.Diag D : NormalGate n m) p)
            (fun w => charOf m (D.eval w) * f w)
          = fun w => K * (charOf m (D.eval w) * pauliAct p f w) :=
      ⟨_, mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
        (inv_ne_zero (pow_ne_zero _ Complex.I_ne_zero)))
        (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))) (charOf_ne_zero _ _),
        fun f => pauliAct_zShearBy_of_shift (by omega) D _ p f c0 hc0⟩
    refine ⟨K⁻¹, fun f => ?_⟩
    funext w
    change charOf m (D.eval w) * pauliAct p f w
      = K⁻¹ * pauliAct (letterLin (NormalGate.Diag D : NormalGate n m) p)
          (fun v => charOf m (D.eval v) * f v) w
    rw [hkey f, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  | Cnot i j =>
    refine ⟨.cnot i j hg, trivial,
      fun p => ⟨(-1) ^ ((p.X i * p.Z j * (1 + p.X j + p.Z i)).val), fun f => ?_⟩⟩
    funext w
    have key := congrFun (pauliAct_cnotPauli hg p f) w
    change pauliAct p f (DiagPhase.cnotBitMap i j w)
      = (-1) ^ ((p.X i * p.Z j * (1 + p.X j + p.Z i)).val)
        * pauliAct (cnotPauli i j p) (fun v => f (DiagPhase.cnotBitMap i j v)) w
    rw [key, ← mul_assoc, hsq, one_mul]

/-- **A well-formed word**, read as a T05 Clifford word, carries every Pauli to its image under
the word's symplectic map times a scalar. -/
private theorem exists_word_intertwining {m : ℕ} (hm : 2 ≤ m) (gs : List (NormalGate n m))
    (hgs : WordWF gs) :
    ∃ W : GateWord n m, (∀ G ∈ W, G.IsClifford) ∧ ∀ p : Pauli n, ∃ c : ℂ, ∀ f,
      runAmp W (pauliAct p f) = fun w => c * pauliAct (wordLin gs p) (runAmp W f) w := by
  induction gs with
  | nil =>
    refine ⟨[], fun G hG => absurd hG List.not_mem_nil, fun p => ⟨1, fun f => ?_⟩⟩
    funext w
    rw [one_mul]
    rfl
  | cons g gs ih =>
    obtain ⟨G, hG, hGp⟩ := exists_letter_intertwining hm g (hgs g (List.mem_cons_self ..))
    obtain ⟨W, hW, hWp⟩ := ih fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    refine ⟨G :: W, fun G' hG' => ?_, fun p => ?_⟩
    · rcases List.mem_cons.mp hG' with rfl | h
      · exact hG
      · exact hW G' h
    · obtain ⟨c₁, hc₁⟩ := hGp p
      obtain ⟨c₂, hc₂⟩ := hWp (letterLin g p)
      refine ⟨c₁ * c₂, fun f => ?_⟩
      rw [runAmp_cons, runAmp_cons, hc₁, runAmp_mul_left, hc₂, wordLin_cons,
        LinearMap.comp_apply]
      funext w
      ring

/-- **The scalar is a sign**: carrying the Pauli twice is the identity on both sides, and the
referee of a word is injective (`runAmp_invWord`). -/
private theorem scalar_sign {m : ℕ} (W : GateWord n m) {p q : Pauli n} {c : ℂ}
    (h : ∀ f, runAmp W (pauliAct p f) = fun w => c * pauliAct q (runAmp W f) w) :
    ∃ s : ZMod 2, c = (-1) ^ s.val := by
  let f₀ : (Fin n → ZMod 2) → ℂ := fun _ => 1
  have hne : runAmp W f₀ ≠ 0 := by
    intro h0
    have hinv := runAmp_invWord W f₀
    rw [h0, runAmp_zero_fun] at hinv
    exact one_ne_zero (congrFun hinv 0).symm
  obtain ⟨w, hw⟩ : ∃ w, runAmp W f₀ w ≠ 0 := Function.ne_iff.mp hne
  have h1 := congrFun (h (pauliAct p f₀)) w
  rw [pauliAct_pauliAct, h f₀, pauliAct_mul_left, pauliAct_pauliAct] at h1
  have hcc : (c * c - 1) * runAmp W f₀ w = 0 := by
    beta_reduce at h1
    linear_combination -h1
  have hc1 : c * c = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hcc).resolve_right hw)
  rcases mul_self_eq_one_iff.mp hc1 with h1 | h1
  · exact ⟨0, by rw [h1, ZMod.val_zero, pow_zero]⟩
  · exact ⟨1, by rw [h1, ZMod.val_one, pow_one]⟩

/-! ## Pauli letters for the signs -/

/-- `X` at bit `b` as three Clifford letters: H, the `Z` letter `CZ_{bb}`, H. -/
private noncomputable def xWord {m : ℕ} (b : Fin n) : GateWord n m :=
  [.hadamard b, .diagonal (DiagPhase.czGate m b b), .hadamard b]

/-- The referee of `xWord b` is `X` at `b`: `H Z H = X`. -/
private theorem runAmp_xWord {m : ℕ} (hm : 1 ≤ m) (b : Fin n) (f : (Fin n → ZMod 2) → ℂ) :
    runAmp (xWord b : GateWord n m) f = pauliAct (paulix b) f := by
  have hz : ∀ h : (Fin n → ZMod 2) → ℂ,
      letterAmp (GateLetter.diagonal (DiagPhase.czGate m b b) : GateLetter n m) h
        = pauliAct (pauliz b) h := by
    intro h
    funext w
    change charOf m ((DiagPhase.czGate m b b).eval w) * h w
      = pauliAct (⟨0, Pi.single b 1⟩ : Pauli n) h w
    rw [charOf_czGate_eval hm, pauliAct_zType, dotF2_single_left]
    rcases zmod_two_eq_zero_or_one (w b) with hb | hb <;> rw [hb]
    · rw [ZMod.val_zero, mul_zero]
    · rw [ZMod.val_one, mul_one]
  have hswap : pauliSwapOn ({b} : Finset (Fin n)) (pauliz b) = paulix b := by
    refine Pauli.ext ?_ ?_ <;> funext i <;> by_cases hi : i = b
    · subst hi
      simp
    · simp [hi]
    · subst hi
      simp
    · simp [hi]
  have key := pauliAct_pauliSwapOn_walshTransform b (pauliz b) (walshTransform b f)
  rw [hswap, walshTransform_involutive b f] at key
  change walshTransform b
      (letterAmp (GateLetter.diagonal (DiagPhase.czGate m b b)) (walshTransform b f)) = _
  rw [hz, key]
  funext w
  rw [pauliz_X, Pi.zero_apply, ZMod.val_zero, zero_mul, pow_zero, one_mul]

/-- `X` at each bit of a list, in order. -/
private noncomputable def xWords {m : ℕ} (B : List (Fin n)) : GateWord n m := B.flatMap xWord

/-- Two Paulis commute up to the sign `(−1)^ω`. -/
private theorem pauliAct_comm_sign (p q : Pauli n) (f : (Fin n → ZMod 2) → ℂ) :
    pauliAct p (pauliAct q f)
      = fun w => (-1 : ℂ) ^ (omega p q).val * pauliAct q (pauliAct p f) w := by
  funext w
  rcases zmod_two_eq_zero_or_one (omega p q) with h | h
  · rw [pauliAct_comm h, h, ZMod.val_zero, pow_zero, one_mul]
  · rw [pauliAct_anticomm h f w, h, ZMod.val_one, pow_one, neg_one_mul, neg_neg]

/-- The `X` letters carry every Pauli to itself, with the sign of its anticommutations. -/
private theorem runAmp_xWords {m : ℕ} (hm : 1 ≤ m) (B : List (Fin n)) (p : Pauli n)
    (f : (Fin n → ZMod 2) → ℂ) :
    runAmp (xWords B : GateWord n m) (pauliAct p f) = fun w =>
      (-1 : ℂ) ^ (B.map fun b => (omega (paulix b) p).val).sum
        * pauliAct p (runAmp (xWords B : GateWord n m) f) w := by
  induction B generalizing f with
  | nil =>
    funext w
    rw [List.map_nil, List.sum_nil, pow_zero, one_mul]
    rfl
  | cons b B ih =>
    have happ : (xWords (b :: B) : GateWord n m) = xWord b ++ xWords B := rfl
    rw [happ, runAmp_append, runAmp_append, runAmp_xWord hm, runAmp_xWord hm,
      pauliAct_comm_sign, runAmp_mul_left, ih, List.map_cons, List.sum_cons, pow_add]
    funext w
    ring

namespace StabCode

/-- The ancillas in `F`, each flipped once: the `Z` of the `j`-th ancilla anticommutes with one
`X` exactly when `j ∈ F`. -/
private theorem sum_omega_ancilla (C : StabCode n r) (F : Finset (Fin r)) (j : Fin r) :
    ((F.toList.map C.ancillaBit).map fun b => (omega (paulix b) (pauliz (C.ancillaBit j))).val).sum
      = if j ∈ F then 1 else 0 := by
  rw [List.map_map]
  have hk : ∀ k, ((fun b => (omega (paulix b) (pauliz (C.ancillaBit j))).val) ∘ C.ancillaBit) k
      = if k = j then 1 else 0 := by
    intro k
    rw [Function.comp_apply, omega_paulix_pauliz]
    by_cases hkj : k = j
    · rw [if_pos (congrArg C.ancillaBit hkj), if_pos hkj, ZMod.val_one]
    · rw [if_neg ((ancillaBit_injective C).ne hkj), if_neg hkj, ZMod.val_zero]
  rw [List.map_congr_left fun k _ => hk k, Finset.sum_map_toList, Finset.sum_ite_eq']

/-- The sign bookkeeping: flipping exactly when `s + t = 1` turns the sign `t` into `s`. -/
private theorem neg_one_pow_flip (s t : ZMod 2) (P : Prop) [Decidable P] (hP : P ↔ s + t = 1) :
    (-1 : ℂ) ^ (if P then 1 else 0) * (-1) ^ t.val = (-1) ^ s.val := by
  by_cases h : P
  · rw [if_pos h]
    have h' := hP.mp h
    rcases zmod_two_eq_zero_or_one s with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one t with rfl | rfl
    · exact absurd h' (by decide)
    · rw [ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, neg_one_mul, neg_neg]
    · rw [ZMod.val_zero, ZMod.val_one, pow_one, pow_zero, mul_one]
    · exact absurd h' (by decide)
  · rw [if_neg h, pow_zero, one_mul]
    have h' : ¬ s + t = 1 := fun h' => h (hP.mpr h')
    rcases zmod_two_eq_zero_or_one s with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one t with rfl | rfl
    · rfl
    · exact absurd (by decide) h'
    · exact absurd (by decide) h'
    · rfl

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:hba0d3b4e9157
-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:hb3871b28d463
/-- **An encoder**: `X` letters on the ancillas whose sign needs flipping, then a Clifford word
realising the symplectic lift (`exists_wordWF_wordLin_eq`). As in the source, the encoder is
fixed by the images of the data's `X` and `Z` and of the ancillas' `Z`; the images of the
ancillas' `X` are whatever the lift gives. -/
private theorem exists_encoder (C : StabCode n r) {m : ℕ} (hm : 2 ≤ m) :
    ∃ w : GateWord n m, C.IsEncoder w := by
  obtain ⟨T, hT, hanc, hlx, hlz⟩ := exists_clifford_lift C
  obtain ⟨gs, hwf, hlin⟩ := exists_wordWF_wordLin_eq hm hT
  obtain ⟨W, hWc, hW⟩ := exists_word_intertwining hm gs hwf
  have hW' : ∀ p : Pauli n, ∃ c : ℂ, ∀ f,
      runAmp W (pauliAct p f) = fun w => c * pauliAct (T p) (runAmp W f) w := fun p => by
    obtain ⟨c, hc⟩ := hW p
    exact ⟨c, fun f => by rw [hc f, hlin]; rfl⟩
  choose c hc using hW'
  choose e he using fun p => scalar_sign W (hc p)
  let F : Finset (Fin r) :=
    Finset.univ.filter fun j => (C.gen j).sign + e (pauliz (C.ancillaBit j)) = 1
  let B : List (Fin n) := F.toList.map C.ancillaBit
  have hcomp : ∀ p f, runAmp (xWords B ++ W) (pauliAct p f) = fun w =>
      ((-1 : ℂ) ^ (B.map fun b => (omega (paulix b) p).val).sum * c p)
        * pauliAct (T p) (runAmp (xWords B ++ W) f) w := by
    intro p f
    rw [runAmp_append, runAmp_append, runAmp_xWords (by omega), runAmp_mul_left, hc]
    funext w
    ring
  refine ⟨xWords B ++ W, ⟨fun G hG => ?_, fun j f => ?_, fun i => ?_, fun i => ?_⟩⟩
  · rcases List.mem_append.mp hG with h | h
    · obtain ⟨b, -, hb⟩ := List.mem_flatMap.mp h
      change G ∈ [GateLetter.hadamard b, GateLetter.diagonal (DiagPhase.czGate m b b),
        GateLetter.hadamard b] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · trivial
      rcases List.mem_cons.mp hb with rfl | hb
      · exact czLetter_wf m b b
      rcases List.mem_cons.mp hb with rfl | hb
      · trivial
      exact absurd hb List.not_mem_nil
    · exact hWc G h
  · rw [hcomp, hanc j]
    change _ = fun w => (-1 : ℂ) ^ (C.gen j).sign.val
      * pauliAct (C.gen j).pauli (runAmp (xWords B ++ W) f) w
    funext w
    congr 1
    have hmem : j ∈ F ↔ (C.gen j).sign + e (pauliz (C.ancillaBit j)) = 1 := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [sum_omega_ancilla, he]
    exact neg_one_pow_flip _ _ _ hmem
  · obtain ⟨s, hs⟩ := scalar_sign _ (hcomp (paulix (C.logicalBit i)))
    exact ⟨⟨s, T (paulix (C.logicalBit i))⟩, hlx i, fun f => by rw [hcomp, hs]; rfl⟩
  · obtain ⟨s, hs⟩ := scalar_sign _ (hcomp (pauliz (C.logicalBit i)))
    exact ⟨⟨s, T (pauliz (C.logicalBit i))⟩, hlz i, fun f => by rw [hcomp, hs]; rfl⟩

/-! ## The encoder's input -/

/-- `pinZero` keeps a positive precision. -/
private theorem pinZero_m {N : ℕ} {S : KernelSumState N} (hm : 1 ≤ S.m) :
    (pinZero S).m = S.m := by
  have hs : ∀ T : KernelSumState (N + 1), (sliceZ (Fin.last N) 0 T).m = T.m := fun T => by
    delta sliceZ
    split <;> rfl
  change (sliceZ (Fin.last N) 0 (condition (appendFreeBit S) (signedZ (Fin.last N)) 0)).m = S.m
  rw [hs, condition_signedZ]
  refine conditionPrecision_eq (signedZ (Fin.last N)) hm fun h => ?_
  rw [yWeight_signedZ] at h
  exact absurd h (by decide)

/-- `pinZeros r S` is a carrier state at `S`'s precision whose amplitude vanishes unless the `r`
appended bits are zero. -/
private theorem pinZeros_spec {N : ℕ} (k : ℕ) {S : KernelSumState N} (hS : IsCarrier S) :
    IsCarrier (pinZeros k S) ∧ (pinZeros k S).m = S.m ∧
      ∀ u, amp (pinZeros k S) u ≠ 0 → ∀ j : Fin k, u (Fin.natAdd N j) = 0 := by
  induction k with
  | zero => exact ⟨hS, rfl, fun _ _ j => j.elim0⟩
  | succ k ih =>
    obtain ⟨hC, hm, hz⟩ := ih
    refine ⟨isCarrier_pinZero hC, (pinZero_m hC.1).trans hm, fun u hu j => ?_⟩
    change amp (pinZero (pinZeros k S)) u ≠ 0 at hu
    rw [amp_pinZero hC] at hu
    beta_reduce at hu
    by_cases hl : u (Fin.last (N + k)) = 0
    · rw [if_pos hl] at hu
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hj : Fin.natAdd N j'.castSucc = (Fin.natAdd N j').castSucc := Fin.ext rfl
        rw [hj]
        exact hz (Fin.init u) hu j'
      · exact hl
    · rw [if_neg hl] at hu
      exact absurd rfl hu

/-- A cast keeps the precision. -/
private theorem castBits_m {N N' : ℕ} (h : N = N') (S : KernelSumState N) :
    (castBits h S).m = S.m := by
  subst h
  rfl

/-- The encoder's input is a carrier state at the input's precision whose amplitude vanishes
unless every ancilla is zero. -/
private theorem encodeInput_spec (C : StabCode n r) {S : KernelSumState (n - r)}
    (hS : IsCarrier S) :
    IsCarrier (C.encodeInput S) ∧ (C.encodeInput S).m = S.m ∧
      ∀ v, amp (C.encodeInput S) v ≠ 0 → ∀ j, v (C.ancillaBit j) = 0 := by
  obtain ⟨hC, hm, hz⟩ := pinZeros_spec r hS
  refine ⟨isCarrier_castBits _ hC, (castBits_m _ _).trans hm, fun v hv j => ?_⟩
  change amp (castBits (Nat.sub_add_cancel C.r_le) (pinZeros r S)) v ≠ 0 at hv
  rw [amp_castBits] at hv
  exact hz _ hv j

/-- The `Z` of a bit fixes every function vanishing where that bit is `1`. -/
private theorem pauliAct_pauliz_of_zero {N : ℕ} (a : Fin N) {φ : (Fin N → ZMod 2) → ℂ}
    (h : ∀ v, φ v ≠ 0 → v a = 0) : pauliAct (pauliz a) φ = φ := by
  funext v
  change pauliAct (⟨0, Pi.single a 1⟩ : Pauli N) φ v = φ v
  rw [pauliAct_zType, dotF2_single_left]
  by_cases hv : φ v = 0
  · rw [hv, mul_zero]
  · rw [h v hv, ZMod.val_zero, pow_zero, one_mul]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h1c4562f2fd60
/-- **Every encoder gives a code state**, as `UMU†` fixes `U|ψ⟩` when `M` fixes `|ψ⟩`: each
ancilla's `Z` fixes the input's amplitude, and the encoder carries it to its generator. -/
private theorem isCodeState_encode {C : StabCode n r} {m : ℕ} {w : GateWord n m}
    (hw : C.IsEncoder w) {S : KernelSumState (n - r)} (hS : IsCarrier S) (hm : S.m = m) :
    C.IsCodeState (amp (C.encode w S)) := by
  obtain ⟨hC, hm', hz⟩ := encodeInput_spec C hS
  intro j
  change (C.gen j).act (amp (run w (C.encodeInput S))) = amp (run w (C.encodeInput S))
  rw [amp_run w hC (hm'.trans hm), ← hw.ancilla j (amp (C.encodeInput S)),
    pauliAct_pauliz_of_zero _ fun v hv => hz v hv j]

end StabCode

/-! ## The encoder's input, padded and as a floor -/

/-- With the last bit zero, the padding to one bit more is the padding of the first bits. -/
private theorem padZero_succ_eq {N M : ℕ} (hN : N ≤ M) (ψ : (Fin N → ZMod 2) → ℂ)
    (w : Fin (M + 1) → ZMod 2) :
    padZero (hN.trans (Nat.le_succ M)) ψ w
      = if w (Fin.last M) = 0 then padZero hN ψ (Fin.init w) else 0 := by
  unfold padZero
  by_cases h : ∀ i : Fin (M + 1), N ≤ i.val → w i = 0
  · have hl : w (Fin.last M) = 0 := h _ (by rw [Fin.val_last]; exact hN)
    have hi : ∀ i : Fin M, N ≤ i.val → Fin.init w i = 0 := fun i hi => h i.castSucc hi
    rw [if_pos h, if_pos hl, if_pos hi]
    rfl
  · rw [if_neg h]
    by_cases hl : w (Fin.last M) = 0
    · have hi : ¬ ∀ i : Fin M, N ≤ i.val → Fin.init w i = 0 := by
        intro hi
        apply h
        intro i hi'
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact hi j hi'
        · exact hl
      rw [if_pos hl, if_neg hi]
    · rw [if_neg hl]

/-- `pinZeros k S` has `S`'s amplitude padded with zeros. -/
private theorem amp_pinZeros {N : ℕ} (k : ℕ) {S : KernelSumState N} (hS : IsCarrier S) :
    amp (pinZeros k S) = padZero (Nat.le_add_right N k) (amp S) := by
  induction k with
  | zero =>
    funext v
    unfold padZero
    rw [if_pos fun i hi => absurd i.isLt (by omega)]
    rfl
  | succ k ih =>
    change amp (pinZero (pinZeros k S)) = padZero ((Nat.le_add_right N k).trans (Nat.le_succ _))
      (amp S)
    rw [amp_pinZero (StabCode.pinZeros_spec k hS).1, ih]
    funext w
    rw [padZero_succ_eq]

namespace StabCode

/-- **The encoder's input has the input's amplitude padded with zeros.** -/
private theorem amp_encodeInput (C : StabCode n r) {S : KernelSumState (n - r)}
    (hS : IsCarrier S) : amp (C.encodeInput S) = padZero (Nat.sub_le n r) (amp S) := by
  have h := Nat.sub_add_cancel C.r_le
  change amp (castBits h (pinZeros r S)) = _
  rw [amp_castBits, amp_pinZeros r hS]
  funext w
  unfold padZero
  have hiff : (∀ i : Fin (n - r + r), n - r ≤ i.val → (w ∘ Fin.cast h) i = 0)
      ↔ ∀ i : Fin n, n - r ≤ i.val → w i = 0 :=
    ⟨fun H i hi => H (Fin.cast h.symm i) hi, fun H i hi => H (Fin.cast h i) hi⟩
  by_cases hc : ∀ i : Fin n, n - r ≤ i.val → w i = 0
  · rw [if_pos (hiff.mpr hc), if_pos hc]
    rfl
  · rw [if_neg (fun H => hc (hiff.mp H)), if_neg hc]

end StabCode

/-- A Pauli whose last `Z` bit is zero acts on a function of the first bits through its first
bits. -/
private theorem pauliAct_init {N : ℕ} {p : Pauli (N + 1)} (hz : p.Z (Fin.last N) = 0)
    (φ : (Fin N → ZMod 2) → ℂ) :
    pauliAct p (fun w => φ (Fin.init w)) = fun w => pauliAct (pauliInit p) φ (Fin.init w) := by
  have hdot : ∀ v : Fin (N + 1) → ZMod 2, zDot p v = zDot (pauliInit p) (Fin.init v) := by
    intro v
    unfold zDot
    rw [Fin.sum_univ_castSucc, hz, ZMod.val_zero, zero_mul, add_zero]
    rfl
  funext w
  unfold pauliAct
  rw [show yWeight p = yWeight (pauliInit p) from hdot p.X, hdot (w + p.X)]
  rfl

/-- **A free bit appended to a floor gives a floor**: the Lagrangian `L ⊕ ⟨X_last⟩` stabilizes
the amplitude, which does not read the last bit, with `L`'s signs. -/
private theorem isFloor_appendFreeBit {N : ℕ} {S : KernelSumState N} (hS : IsFloor S) :
    IsFloor (appendFreeBit S) := by
  refine ⟨isCarrier_appendFreeBit hS.1, fun p hp => ?_⟩
  obtain ⟨hpL, hpZ⟩ := Submodule.mem_inf.mp hp
  obtain ⟨s, hs⟩ := hS.2 _ (Submodule.mem_comap.mp hpL)
  refine ⟨s, ?_⟩
  rw [amp_appendFreeBit, pauliAct_init (LinearMap.mem_ker.mp hpZ), hs]

/-- **`pinZero` of a floor is `StateEq` to a floor**: the appended floor conditioned on `Z` at
the last bit, a nonzero amplitude, is one (`isFloor_condition`). -/
private theorem exists_floor_pinZero {N : ℕ} {S : KernelSumState N} (hS : IsFloor S) :
    ∃ T : KernelSumState (N + 1), IsFloor T ∧ amp T = amp (pinZero S) := by
  have hA := isFloor_appendFreeBit hS
  have hampC : amp (condition (appendFreeBit S) (signedZ (Fin.last N)) 0) = amp (pinZero S) := by
    rw [amp_pinZero hS.1]
    funext v
    rw [amp_condition _ hA.1.2.2.1]
    refine (pauliProjection_zPauli_single (Fin.last N) 0 (amp (appendFreeBit S)) v).trans ?_
    rw [amp_appendFreeBit]
  rcases isFloor_condition hA (signedZ (Fin.last N)) 0 with h0 | ⟨T, -, hT, hST⟩
  · exact absurd (hampC.symm.trans h0) (isCarrier_pinZero hS.1).2.2.2
  · exact ⟨T, hT, (show amp _ = amp T from hST).symm.trans hampC⟩

/-- `pinZeros k` of a floor has a floor's amplitude. -/
private theorem exists_floor_pinZeros {N : ℕ} (k : ℕ) {S : KernelSumState N} (hS : IsFloor S) :
    ∃ T : KernelSumState (N + k), IsFloor T ∧ amp T = amp (pinZeros k S) := by
  induction k with
  | zero => exact ⟨S, hS, rfl⟩
  | succ k ih =>
    obtain ⟨T, hT, hTa⟩ := ih
    obtain ⟨T', hT', hT'a⟩ := exists_floor_pinZero hT
    refine ⟨T', hT', ?_⟩
    change _ = amp (pinZero (pinZeros k S))
    rw [hT'a, amp_pinZero hT.1, amp_pinZero (StabCode.pinZeros_spec k hS.1).1, hTa]

/-- A cast keeps a floor. -/
private theorem isFloor_castBits {N N' : ℕ} (h : N = N') {S : KernelSumState N}
    (hS : IsFloor S) : IsFloor (castBits h S) := by
  subst h
  exact hS

/-- **The encoder's input of a floor has a floor's amplitude.** -/
private theorem StabCode.exists_floor_encodeInput (C : StabCode n r) {S : KernelSumState (n - r)}
    (hS : IsFloor S) : ∃ T : KernelSumState n, IsFloor T ∧ amp T = amp (C.encodeInput S) := by
  obtain ⟨T, hT, hTa⟩ := exists_floor_pinZeros r hS
  have h := Nat.sub_add_cancel C.r_le
  refine ⟨castBits h T, isFloor_castBits h hT, ?_⟩
  change _ = amp (castBits h (pinZeros r S))
  rw [amp_castBits, amp_castBits, hTa]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:hb3871b28d463
-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:hba0d3b4e9157
/-- **Every code has an encoder** at every precision of at least `2`, where the `S` letter lives.
The source realises any automorphism of the Pauli group by a Clifford and uses it to encode into
any stabilizer code; here the route is the library's symplectic lift: a symplectic basis of
`Pauli n` whose last `r` `Z`-images are the generators' Pauli parts, a word realising it
(`spGeneratedByCliffordGates`), and Pauli letters for the signs. -/
theorem encoder_exists (C : StabCode n r) {m : ℕ} (hm : 2 ≤ m) :
    ∃ w : GateWord n m, C.IsEncoder w :=
  StabCode.exists_encoder C hm

/-- **Any carrier state encodes, at its own height**: at the word's precision, at any height and
for any word, the encoding is a carrier state, and its amplitude is the word's referee on the
input's amplitude with the ancillas padded with zeros. -/
theorem isCarrier_encode (C : StabCode n r) {m : ℕ} (w : GateWord n m)
    {S : KernelSumState (n - r)} (hS : IsCarrier S) (hm : S.m = m) :
    IsCarrier (C.encode w S)
      ∧ amp (C.encode w S) = runAmp w (padZero (Nat.sub_le n r) (amp S)) := by
  obtain ⟨hC, hm', -⟩ := StabCode.encodeInput_spec C hS
  refine ⟨isCarrier_run w hC (hm'.trans hm), ?_⟩
  change amp (run w (C.encodeInput S)) = _
  rw [amp_run w hC (hm'.trans hm), StabCode.amp_encodeInput C hS]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h1c4562f2fd60
/-- **Every encoder gives a code state**: run on `pinZeros r S`, each ancilla's `Z` fixes the
input and is carried to its generator, which therefore fixes the encoding. -/
theorem encode_isCodeState {C : StabCode n r} {m : ℕ} {w : GateWord n m} (hw : C.IsEncoder w)
    {S : KernelSumState (n - r)} (hS : IsCarrier S) (hm : S.m = m) :
    C.IsCodeState (amp (C.encode w S)) :=
  StabCode.isCodeState_encode hw hS hm

/-! ## Clifford letters carry stabilizers along -/

/-- At precision `0` every phase is `1`: the exponent ring is trivial. -/
private theorem charOf_prec_zero (z : ZMod (2 ^ 0)) : charOf 0 z = 1 := by
  unfold charOf
  have h : z.val = 0 := by
    haveI : NeZero (2 ^ 0) := ⟨by norm_num⟩
    have hlt := ZMod.val_lt z
    norm_num at hlt
    rw [hlt]
    exact ZMod.val_zero
  rw [h]
  simp

/-- **A Clifford letter carries every Pauli to its image under an injective linear map, times a
scalar**: H by the swap at its bit, a diagonal letter by the shear of its polar matrix (at
precision `0` the letter is the identity), CNOT by its symplectic lift. -/
private theorem exists_letter_carry {m : ℕ} (G : GateLetter n m) (hG : G.IsClifford) :
    ∃ Λ : Pauli n →ₗ[ZMod 2] Pauli n, Function.Injective Λ ∧ ∀ p : Pauli n, ∃ c : ℂ, ∀ f,
      letterAmp G (pauliAct p f) = fun w => c * pauliAct (Λ p) (letterAmp G f) w := by
  have hsq : ∀ k : ℕ, ((-1 : ℂ) ^ k) * ((-1) ^ k) = 1 := fun k => by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  cases G with
  | hadamard k =>
    refine ⟨letterLin (NormalGate.H k : NormalGate n m),
      Function.LeftInverse.injective (letterLin_involutive _ trivial), fun p =>
        ⟨(-1) ^ ((p.X k).val * (p.Z k).val), fun f => ?_⟩⟩
    funext w
    have key := congrFun (pauliAct_pauliSwapOn_walshTransform k p f) w
    change walshTransform k (pauliAct p f) w
      = (-1) ^ ((p.X k).val * (p.Z k).val) * pauliAct (pauliSwapOn {k} p) (walshTransform k f) w
    rw [key, ← mul_assoc, hsq, one_mul]
  | diagonal D =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨LinearMap.id, Function.injective_id, fun p => ⟨1, fun f => ?_⟩⟩
      have h1 : (fun v => charOf 0 (D.eval v) * f v) = f := funext fun v => by
        rw [charOf_prec_zero, one_mul]
      funext w
      change charOf 0 (D.eval w) * pauliAct p f w
        = 1 * pauliAct p (fun v => charOf 0 (D.eval v) * f v) w
      rw [h1, charOf_prec_zero, one_mul]
    · refine ⟨letterLin (NormalGate.Diag D : NormalGate n m),
        Function.LeftInverse.injective (letterLin_involutive _ hG), fun p => ?_⟩
      obtain ⟨c0, hc0⟩ := diagShiftDatumBy_polarMatrix D hG ⊤ p.X Submodule.mem_top
      obtain ⟨K, hK, hkey⟩ : ∃ K : ℂ, K ≠ 0 ∧ ∀ f : (Fin n → ZMod 2) → ℂ,
          pauliAct (letterLin (NormalGate.Diag D : NormalGate n m) p)
              (fun w => charOf m (D.eval w) * f w)
            = fun w => K * (charOf m (D.eval w) * pauliAct p f w) :=
        ⟨_, mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
          (inv_ne_zero (pow_ne_zero _ Complex.I_ne_zero)))
          (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))) (charOf_ne_zero _ _),
          fun f => pauliAct_zShearBy_of_shift hm D _ p f c0 hc0⟩
      refine ⟨K⁻¹, fun f => ?_⟩
      funext w
      change charOf m (D.eval w) * pauliAct p f w
        = K⁻¹ * pauliAct (letterLin (NormalGate.Diag D : NormalGate n m) p)
            (fun v => charOf m (D.eval v) * f v) w
      rw [hkey f, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  | cnot i j hij =>
    refine ⟨letterLin (NormalGate.Cnot i j : NormalGate n m),
      Function.LeftInverse.injective (letterLin_involutive _ hij),
      fun p => ⟨(-1) ^ ((p.X i * p.Z j * (1 + p.X j + p.Z i)).val), fun f => ?_⟩⟩
    funext w
    have key := congrFun (pauliAct_cnotPauli hij p f) w
    change pauliAct p f (DiagPhase.cnotBitMap i j w)
      = (-1) ^ ((p.X i * p.Z j * (1 + p.X j + p.Z i)).val)
        * pauliAct (cnotPauli i j p) (fun v => f (DiagPhase.cnotBitMap i j v)) w
    rw [key, ← mul_assoc, hsq, one_mul]

/-- **A word of Clifford letters carries every Pauli to its image under an injective linear map,
times a scalar**, letter by letter. -/
private theorem exists_word_carry {m : ℕ} (W : GateWord n m) (hW : ∀ G ∈ W, G.IsClifford) :
    ∃ T : Pauli n →ₗ[ZMod 2] Pauli n, Function.Injective T ∧ ∀ p : Pauli n, ∃ c : ℂ, ∀ f,
      runAmp W (pauliAct p f) = fun w => c * pauliAct (T p) (runAmp W f) w := by
  induction W with
  | nil =>
    refine ⟨LinearMap.id, Function.injective_id, fun p => ⟨1, fun f => ?_⟩⟩
    funext w
    rw [one_mul]
    rfl
  | cons G W ih =>
    obtain ⟨Λ, hΛ, hGp⟩ := exists_letter_carry G (hW G (List.mem_cons_self ..))
    obtain ⟨T, hT, hWp⟩ := ih fun G' hG' => hW G' (List.mem_cons_of_mem G hG')
    refine ⟨T.comp Λ, hT.comp hΛ, fun p => ?_⟩
    obtain ⟨c₁, hc₁⟩ := hGp p
    obtain ⟨c₂, hc₂⟩ := hWp (Λ p)
    refine ⟨c₁ * c₂, fun f => ?_⟩
    rw [runAmp_cons, runAmp_cons, hc₁, runAmp_mul_left, hc₂, LinearMap.comp_apply]
    funext w
    ring

/-- **A word of Clifford letters carries every Pauli to a Pauli with its sign**, its image under
an injective linear map: the scalar is a sign (`scalar_sign`). -/
private theorem exists_carriesPauli {m : ℕ} {W : GateWord n m} (hW : ∀ G ∈ W, G.IsClifford) :
    ∃ T : Pauli n →ₗ[ZMod 2] Pauli n, Function.Injective T ∧
      ∀ p : Pauli n, ∃ Q : SignedPauli n, Q.pauli = T p ∧ CarriesPauli W p Q := by
  obtain ⟨T, hT, hc⟩ := exists_word_carry W hW
  refine ⟨T, hT, fun p => ?_⟩
  obtain ⟨c, hcp⟩ := hc p
  obtain ⟨s, hs⟩ := scalar_sign W hcp
  exact ⟨⟨s, T p⟩, rfl, fun f => by rw [hcp, hs]; rfl⟩

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h1c4562f2fd60
/-- **Stabilizers are carried along**: if `M` stabilizes `f` with signs, its image under the
word's map stabilizes the word's referee on `f`, as `UMU†` fixes `U|ψ⟩` when `M` fixes `|ψ⟩`. -/
private theorem stabilizedBy_map_carry {m : ℕ} {W : GateWord n m}
    {T : Pauli n →ₗ[ZMod 2] Pauli n}
    (hT : ∀ p : Pauli n, ∃ Q : SignedPauli n, Q.pauli = T p ∧ CarriesPauli W p Q)
    {M : Submodule (ZMod 2) (Pauli n)} {f : (Fin n → ZMod 2) → ℂ} (hs : StabilizedBy M f) :
    StabilizedBy (M.map T) (runAmp W f) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
  obtain ⟨s, hsp⟩ := hs p hp
  obtain ⟨Q, hQ, hc⟩ := hT p
  have h := hc f
  rw [hsp, runAmp_mul_left] at h
  have hsq : ((-1 : ℂ) ^ Q.sign.val) * ((-1) ^ Q.sign.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  refine ⟨Q.sign + s, ?_⟩
  rw [← hQ]
  funext w
  have hw := congrFun h w
  change (-1 : ℂ) ^ s.val * runAmp W f w
    = (-1) ^ Q.sign.val * pauliAct Q.pauli (runAmp W f) w at hw
  rw [neg_one_pow_val_add]
  linear_combination (-((-1 : ℂ) ^ Q.sign.val)) * hw - pauliAct Q.pauli (runAmp W f) w * hsq

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h4fd9476e182c
/-- **An element of `L` acts on every code state as one scalar**, as the source's `S` fixes the
code space: on a generator its sign, on a sum the product by the composition law. -/
private theorem StabCode.exists_scalar (C : StabCode n r) {l : Pauli n} (hl : l ∈ C.L) :
    ∃ c : ℂ, ∀ f, C.IsCodeState f → pauliAct l f = fun w => c * f w := by
  induction hl using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨(-1) ^ (C.gen j).sign.val, fun f hf => ?_⟩
    funext w
    have h := congrFun (hf j) w
    change (-1 : ℂ) ^ (C.gen j).sign.val * pauliAct (C.gen j).pauli f w = f w at h
    have hsq : ((-1 : ℂ) ^ (C.gen j).sign.val) * ((-1) ^ (C.gen j).sign.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination (-1 : ℂ) ^ (C.gen j).sign.val * h - pauliAct (C.gen j).pauli f w * hsq
  | zero =>
    refine ⟨1, fun f _ => ?_⟩
    rw [pauliAct_zero]
    funext w
    rw [one_mul]
  | add x y _ _ ihx ihy =>
    obtain ⟨cx, hx⟩ := ihx
    obtain ⟨cy, hy⟩ := ihy
    refine ⟨(Complex.I ^ (betaFrame y x).val)⁻¹ * (cy * cx), fun f hf => ?_⟩
    have h := pauliAct_add x y f
    rw [hy f hf, pauliAct_mul_left, hx f hf] at h
    have hI : Complex.I ^ (betaFrame y x).val ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
    funext w
    have hw := congrFun h w
    beta_reduce at hw
    rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ hI]
    linear_combination -hw
  | smul a x _ ihx =>
    rcases zmod_two_eq_zero_or_one a with rfl | rfl
    · refine ⟨1, fun f _ => ?_⟩
      rw [zero_smul, pauliAct_zero]
      funext w
      rw [one_mul]
    · rw [one_smul]
      exact ihx

/-- A nonzero code state is stabilized by `L` with signs. -/
private theorem StabCode.stabilizedBy_of_isCodeState (C : StabCode n r)
    {f : (Fin n → ZMod 2) → ℂ} (hf : f ≠ 0) (hc : C.IsCodeState f) : StabilizedBy C.L f :=
  fun _ hl =>
    let ⟨_, hcl⟩ := C.exists_scalar hl
    exists_sign_of_pauliAct_eq hf (hcl f hc)

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h1c4562f2fd60
/-- **A floor encodes to a floor whose Lagrangian contains the stabilizer**, up to `StateEq`: the
run itself need not be a floor (H by the free rule keeps the Lagrangian and adds a bound bit). -/
theorem encode_floor {C : StabCode n r} {m : ℕ} {w : GateWord n m} (hw : C.IsEncoder w)
    {S : KernelSumState (n - r)} (hS : IsFloor S) (hm : S.m = m) :
    ∃ T : KernelSumState n, IsFloor T ∧ StateEq (C.encode w S) T ∧ C.frame.L ≤ T.L := by
  obtain ⟨hC, hm', -⟩ := StabCode.encodeInput_spec C hS.1
  obtain ⟨T₀, hT₀, hT₀a⟩ := C.exists_floor_encodeInput hS
  obtain ⟨Tm, hTinj, hTc⟩ := exists_carriesPauli hw.clifford
  have hg : amp (C.encode w S) = runAmp w (amp T₀) := by
    rw [hT₀a]
    exact amp_run w hC (hm'.trans hm)
  have hg0 : amp (C.encode w S) ≠ 0 := (isCarrier_encode C w hS.1 hm).1.2.2.2
  have hsM : StabilizedBy (T₀.L.map Tm) (amp (C.encode w S)) := by
    rw [hg]
    exact stabilizedBy_map_carry hTc hT₀.2
  have hiso : IsStabilizer (T₀.L.map Tm) := isStabilizer_of_stabilizedBy hg0 hsM
  have hrank : Module.finrank (ZMod 2) (T₀.L.map Tm) = n := by
    exact (Submodule.equivMapOfInjective Tm hTinj T₀.L).finrank_eq.symm.trans
      (finrank_eq_of_isCarrier hT₀.1)
  obtain ⟨T, -, hT, hTa⟩ := exists_floor_of_stabilizedBy hiso
    (orthogonal_le_of_lagrangian hiso hrank) hg0 hsM
  have hTL : T.L = T₀.L.map Tm := by
    refine eq_of_stabilizedBy_of_stabilizedBy (finrank_eq_of_isCarrier hT.1) hrank
      hT.1.2.2.2 hT.2 ?_
    rw [hTa]
    exact hsM
  refine ⟨T, hT, hTa.symm, ?_⟩
  have hsL := C.stabilizedBy_of_isCodeState hg0 (encode_isCodeState hw hS.1 hm)
  have hsup := stabilizedBy_sup hg0 hsM hsL
  have hle := finrank_le_of_isStabilizer (isStabilizer_of_stabilizedBy hg0 hsup)
  have heq : T₀.L.map Tm = T₀.L.map Tm ⊔ C.L :=
    Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
  rw [hTL, StabCode.frame_L]
  exact le_sup_right.trans heq.ge

/-! ## Logical Paulis -/

/-- **A Pauli on `k` bits read on `N` bits**: itself on the first `k`, the identity on the rest;
used with `k ≤ N`. -/
def padPauli {k : ℕ} (N : ℕ) (P : Pauli k) : Pauli N :=
  ⟨fun b => if h : (b : ℕ) < k then P.X ⟨b, h⟩ else 0,
    fun b => if h : (b : ℕ) < k then P.Z ⟨b, h⟩ else 0⟩

/-- **`R` represents the bare Pauli `P` on the input under the word `w`**: `w` carries `P ⊗ I`
to some Pauli with its sign `Q`, and `R` differs from `Q`'s Pauli part by an element of `L`. A
representative is unsigned (`Pauli n`), so it fixes its action only up to a sign. -/
def StabCode.IsLogicalRep (C : StabCode n r) {m : ℕ} (w : GateWord n m) (P : Pauli (n - r))
    (R : Pauli n) : Prop :=
  ∃ Q : SignedPauli n, CarriesPauli w (padPauli n P) Q ∧ R + Q.pauli ∈ C.L

/-- The Z-part dot product of a padded Pauli reads the first bits. -/
private theorem zDot_padPauli {k N : ℕ} (hk : k ≤ N) (P : Pauli k) (v : Fin N → ZMod 2) :
    zDot (padPauli N P) v = zDot P fun i => v (Fin.castLE hk i) := by
  unfold zDot
  symm
  refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ ?_
  · intro b hb
    have hbk : ¬ (b : ℕ) < k := fun h => hb ⟨⟨b, h⟩, Fin.ext rfl⟩
    change ((if h : (b : ℕ) < k then P.Z ⟨b, h⟩ else 0 : ZMod 2)).val * (v b).val = 0
    rw [dif_neg hbk, ZMod.val_zero, zero_mul]
  · intro i
    change (P.Z i).val * _
      = ((if h : ((Fin.castLE hk i : Fin N) : ℕ) < k then P.Z ⟨_, h⟩ else 0 : ZMod 2)).val * _
    rw [dif_pos (show ((Fin.castLE hk i : Fin N) : ℕ) < k from i.isLt)]
    rfl

/-- **A padded Pauli acts on a padded function as the Pauli on the function, padded.** -/
private theorem pauliAct_padPauli {k N : ℕ} (hk : k ≤ N) (P : Pauli k)
    (φ : (Fin k → ZMod 2) → ℂ) :
    pauliAct (padPauli N P) (padZero hk φ) = padZero hk (pauliAct P φ) := by
  have hX : ∀ i : Fin N, k ≤ i.val → (padPauli N P).X i = 0 := fun i hi => by
    change (if h : (i : ℕ) < k then P.X ⟨i, h⟩ else 0) = 0
    rw [dif_neg (by omega)]
  have hXc : (fun i : Fin k => (padPauli N P).X (Fin.castLE hk i)) = P.X := by
    funext i
    change (if h : ((Fin.castLE hk i : Fin N) : ℕ) < k then P.X ⟨_, h⟩ else 0) = P.X i
    rw [dif_pos (show ((Fin.castLE hk i : Fin N) : ℕ) < k from i.isLt)]
    rfl
  have hy : yWeight (padPauli N P) = yWeight P := by
    unfold yWeight
    rw [zDot_padPauli hk, hXc]
  have hiff : ∀ w : Fin N → ZMod 2, (∀ i : Fin N, k ≤ i.val → (w + (padPauli N P).X) i = 0)
      ↔ ∀ i : Fin N, k ≤ i.val → w i = 0 := fun w =>
    forall_congr' fun i => imp_congr_right fun hi => by rw [Pi.add_apply, hX i hi, add_zero]
  funext w
  unfold pauliAct padZero
  by_cases hc : ∀ i : Fin N, k ≤ i.val → w i = 0
  · rw [if_pos ((hiff w).mpr hc), if_pos hc, hy, zDot_padPauli hk]
    have harg : (fun i : Fin k => (w + (padPauli N P).X) (Fin.castLE hk i))
        = (fun i => w (Fin.castLE hk i)) + P.X := by
      rw [← hXc]
      rfl
    rw [harg]
  · rw [if_neg (fun h => hc ((hiff w).mp h)), if_neg hc, mul_zero]

/-- **The encoder's word on any padded function gives a code state**: each ancilla's `Z` fixes the
padded function and the encoder carries it to its generator. -/
private theorem StabCode.isCodeState_runAmp_padZero {C : StabCode n r} {m : ℕ}
    {w : GateWord n m} (hw : C.IsEncoder w) (φ : (Fin (n - r) → ZMod 2) → ℂ) :
    C.IsCodeState (runAmp w (padZero (Nat.sub_le n r) φ)) := by
  intro j
  have hz : ∀ v, padZero (Nat.sub_le n r) φ v ≠ 0 → v (C.ancillaBit j) = 0 := by
    intro v hv
    unfold padZero at hv
    by_cases hc : ∀ i : Fin n, n - r ≤ i.val → v i = 0
    · exact hc _ (Nat.le_add_right (n - r) j.val)
    · rw [if_neg hc] at hv
      exact absurd rfl hv
  rw [← hw.ancilla j (padZero (Nat.sub_le n r) φ), StabCode.pauliAct_pauliz_of_zero _ hz]

/-- A Pauli with its sign is an involution. -/
private theorem signedAct_signedAct (Q : SignedPauli n) (f : (Fin n → ZMod 2) → ℂ) :
    Q.act (Q.act f) = f := by
  have hsq : ((-1 : ℂ) ^ Q.sign.val) * ((-1) ^ Q.sign.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  funext w
  change (-1 : ℂ) ^ Q.sign.val
      * pauliAct Q.pauli (fun v => (-1 : ℂ) ^ Q.sign.val * pauliAct Q.pauli f v) w = f w
  rw [pauliAct_mul_left, pauliAct_pauliAct]
  beta_reduce
  rw [← mul_assoc, hsq, one_mul]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h4fd9476e182c
/-- **A representative acts on code states through `L`**: for `R + Q ∈ L`, `R` after `Q` acts on
every code state as one scalar, since only `N(S)/S` acts on the code space. -/
private theorem StabCode.exists_scalar_rep (C : StabCode n r) {R : Pauli n} {Q : SignedPauli n}
    (hRQ : R + Q.pauli ∈ C.L) :
    ∃ κ : ℂ, ∀ f, C.IsCodeState f → pauliAct R (Q.act f) = fun w => κ * f w := by
  obtain ⟨c, hc⟩ := C.exists_scalar hRQ
  refine ⟨(-1) ^ Q.sign.val * (Complex.I ^ (betaFrame Q.pauli R).val * c), fun f hf => ?_⟩
  change pauliAct R (fun w => (-1 : ℂ) ^ Q.sign.val * pauliAct Q.pauli f w) = _
  rw [pauliAct_mul_left, pauliAct_add, hc f hf]
  funext w
  beta_reduce
  ring

/-- The canonical section's element acts as the Hermitian Pauli. -/
private theorem act_sec (R : Pauli n) (f : (Fin n → ZMod 2) → ℂ) :
    (PauliGroup.sec R).act f = pauliAct R f := by
  funext w
  change Complex.I ^ (0 : ZMod 4).val * pauliAct R f w = pauliAct R f w
  rw [ZMod.val_zero, pow_zero, one_mul]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h4fd9476e182c
-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h5294693efc7d
/-- **A logical Pauli acts as the bare Pauli, up to the sign its representative fixes.** For a
bare Pauli `P` on the input: every representative `R`, applied by `applyPauli` as the Hermitian
Pauli `⟨0, R⟩`, acts on the encoding of every carrier state at the word's precision as `P` on the
input times one sign `(−1)^s`, the same for every input; and some representative with its sign
acts exactly as `P`. On the code of `−Z₁Z₂`, `Z₁` and `Z₂` both represent `Z̄` with opposite
signs. -/
theorem encode_logical {C : StabCode n r} {m : ℕ} {w : GateWord n m} (hw : C.IsEncoder w)
    (P : Pauli (n - r)) :
    (∀ R : Pauli n, C.IsLogicalRep w P R → ∃ s : ZMod 2, ∀ S : KernelSumState (n - r),
        IsCarrier S → S.m = m →
          amp (applyPauli (PauliGroup.sec R) (C.encode w S))
            = (-1 : ℂ) ^ s.val • runAmp w (padZero (Nat.sub_le n r) (pauliAct P (amp S))))
      ∧ ∃ R : SignedPauli n, C.IsLogicalRep w P R.pauli ∧ ∀ S : KernelSumState (n - r),
        IsCarrier S → S.m = m →
          amp (applyPauli R.toPauliGroup (C.encode w S))
            = runAmp w (padZero (Nat.sub_le n r) (pauliAct P (amp S))) := by
  have hk := Nat.sub_le n r
  have hampE : ∀ S : KernelSumState (n - r), IsCarrier S → S.m = m →
      amp (C.encode w S) = runAmp w (padZero hk (amp S)) :=
    fun S hS hm => (isCarrier_encode C w hS hm).2
  have hcarry : ∀ Q : SignedPauli n, CarriesPauli w (padPauli n P) Q →
      ∀ φ, runAmp w (padZero hk (pauliAct P φ)) = Q.act (runAmp w (padZero hk φ)) := by
    intro Q hQ φ
    rw [← pauliAct_padPauli hk]
    exact hQ _
  constructor
  · rintro R ⟨Q, hQ, hRQ⟩
    obtain ⟨κ, hκ⟩ := C.exists_scalar_rep hRQ
    have key : ∀ φ, pauliAct R (runAmp w (padZero hk φ))
        = fun x => κ * runAmp w (padZero hk (pauliAct P φ)) x := by
      intro φ
      have h1 : runAmp w (padZero hk φ) = Q.act (runAmp w (padZero hk (pauliAct P φ))) := by
        rw [← hcarry Q hQ, pauliAct_pauliAct]
      rw [h1]
      exact hκ _ (StabCode.isCodeState_runAmp_padZero hw _)
    by_cases hex : ∃ S₀ : KernelSumState (n - r), IsCarrier S₀ ∧ S₀.m = m
    · obtain ⟨S₀, hS₀, hm₀⟩ := hex
      have hg₀ : runAmp w (padZero hk (amp S₀)) ≠ 0 := by
        rw [← hampE S₀ hS₀ hm₀]
        exact (isCarrier_encode C w hS₀ hm₀).1.2.2.2
      have h2 := key (pauliAct P (amp S₀))
      rw [pauliAct_pauliAct] at h2
      have h3 := pauliAct_pauliAct R (runAmp w (padZero hk (amp S₀)))
      rw [key, pauliAct_mul_left, h2] at h3
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hg₀
      have h3x := congrFun h3 x
      beta_reduce at h3x
      have hsq : κ * κ = 1 := mul_right_cancel₀ hx (by linear_combination h3x)
      obtain ⟨s, hs⟩ := exists_sign_of_mul_self hsq
      refine ⟨s, fun S hS hm => ?_⟩
      rw [amp_applyPauli, act_sec, hampE S hS hm, key, hs]
      rfl
    · exact ⟨0, fun S hS hm => absurd ⟨S, hS, hm⟩ hex⟩
  · obtain ⟨_, _, hT⟩ := exists_carriesPauli hw.clifford
    obtain ⟨Q, -, hQ⟩ := hT (padPauli n P)
    refine ⟨Q, ⟨Q, hQ, ?_⟩, fun S hS hm => ?_⟩
    · rw [pauli_add_self]
      exact C.L.zero_mem
    · rw [amp_applyPauli, act_toPauliGroup, hampE S hS hm, hcarry Q hQ]

/-! ## Renaming the bits of a letter -/

/-- **A letter moved along an injective bit map** `ι`: H and CNOT at the image bits, a diagonal
exponent with its variables renamed; injectivity keeps CNOT's two bits distinct. -/
noncomputable def GateLetter.renameBits {N m : ℕ} (ι : Fin n → Fin N)
    (hι : Function.Injective ι) : GateLetter n m → GateLetter N m
  | .hadamard i => .hadamard (ι i)
  | .diagonal D => .diagonal (MvPolynomial.rename ι D)
  | .cnot i j hij => .cnot (ι i) (ι j) (hι.ne hij)

/-- `secondHalfBit` is injective. -/
theorem secondHalfBit_injective (n k : ℕ) : Function.Injective (secondHalfBit n k) :=
  fun _ _ h => (Fin.natAdd_inj n).mp (Fin.cast_injective _ h)

/-- **`secondHalfLetter` is a renaming**, along `secondHalfBit`. -/
theorem secondHalfLetter_eq_renameBits (n : ℕ) {k M : ℕ} :
    (secondHalfLetter n : GateLetter (n + k) M → GateLetter ((n + n) + k) M)
      = GateLetter.renameBits (secondHalfBit n k) (secondHalfBit_injective n k) := by
  funext g
  cases g <;> rfl

/-! ## Registers of blocks -/

/-- **States appended in order**, block `0` first, by T46's `appendState`, starting from T46's
unit `idState 0`, the amplitude `1` on no bits, which is also the value at no blocks. -/
noncomputable def appendStates :
    {b : ℕ} → {N : Fin b → ℕ} → ((t : Fin b) → KernelSumState (N t)) → KernelSumState (∑ t, N t)
  | 0, _, _ => castBits (by simp) (idState 0)
  | b + 1, N, F => castBits (Fin.sum_univ_castSucc N).symm
      (appendState (appendStates fun t => F (Fin.castSucc t)) (F (Fin.last b)))

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h91b92ec7d0c6
/-- **A register of `b` blocks**: block `t` holds a code on `blockSize t` bits with
`generatorCount t` generators. The source encodes several copies of one code side by side; the
blocks here may hold different codes. -/
structure Register (b : ℕ) where
  /-- The number of bits of block `t`. -/
  blockSize : Fin b → ℕ
  /-- The number of generators of block `t`'s code. -/
  generatorCount : Fin b → ℕ
  /-- The code of block `t`. -/
  code : (t : Fin b) → StabCode (blockSize t) (generatorCount t)

namespace Register

variable {b : ℕ}

/-- The register's bits, every block's. -/
abbrev totalBits (R : Register b) : ℕ := ∑ t, R.blockSize t

/-- The register's logical bits, every block's. -/
abbrev logicalCount (R : Register b) : ℕ := ∑ t, (R.blockSize t - R.generatorCount t)

/-- The register's ancillas, every block's. -/
abbrev ancillaCount (R : Register b) : ℕ := ∑ t, R.generatorCount t

/-- The logical bits and the ancillas are all the bits. -/
theorem logicalCount_add_ancillaCount (R : Register b) :
    R.logicalCount + R.ancillaCount = R.totalBits := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => Nat.sub_add_cancel (R.code t).r_le

/-- **Bit `j` of block `t`** on the register, block-major. -/
def bit (R : Register b) (t : Fin b) (j : Fin (R.blockSize t)) : Fin R.totalBits :=
  finSigmaFinEquiv ⟨t, j⟩

/-- A block's bits are distinct on the register. -/
theorem bit_injective (R : Register b) (t : Fin b) : Function.Injective (R.bit t) := by
  intro j j' h
  have h' := finSigmaFinEquiv.injective h
  simpa using h'

/-- **The register's layout**: the input's bits, the logical bits block-major then the ancillas
block-major, moved into their blocks, block `t`'s logical bits first and its ancillas last, as
its encoder reads them (`StabCode.logicalBit`, `StabCode.ancillaBit`). -/
def layout (R : Register b) : Fin (R.logicalCount + R.ancillaCount) ≃ Fin R.totalBits :=
  finSumFinEquiv.symm.trans <|
    (Equiv.sumCongr
        (finSigmaFinEquiv (n := fun t => R.blockSize t - R.generatorCount t)).symm
        (finSigmaFinEquiv (n := R.generatorCount)).symm).trans <|
      (Equiv.sigmaSumDistrib _ _).symm.trans <|
        (Equiv.sigmaCongrRight fun t =>
            finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel (R.code t).r_le))).trans
          (finSigmaFinEquiv (n := R.blockSize))

/-- **The register's input**: the logical input with every ancilla appended and held at zero
(`pinZeros`), moved into its block by the fixed reindexing `layout`. -/
noncomputable def input (R : Register b) (S : KernelSumState R.logicalCount) :
    KernelSumState R.totalBits :=
  reindexFreeBits R.logicalCount_add_ancillaCount R.layout (pinZeros R.ancillaCount S)

/-- **The blockwise word**: each block's word renamed into its block, the words concatenated,
block `0` first. -/
noncomputable def word (R : Register b) {m : ℕ}
    (ws : (t : Fin b) → GateWord (R.blockSize t) m) : GateWord R.totalBits m :=
  (List.finRange b).flatMap fun t =>
    (ws t).map (GateLetter.renameBits (R.bit t) (R.bit_injective t))

/-- **The blockwise encoding**: the blockwise word run on the register's input. -/
noncomputable def blockEncode (R : Register b) {m : ℕ}
    (ws : (t : Fin b) → GateWord (R.blockSize t) m) (S : KernelSumState R.logicalCount) :
    KernelSumState R.totalBits :=
  run (R.word ws) (R.input S)

end Register

/-! ## The blockwise encoder on a product input: the proof -/

/-- A renamed letter acts on a function of the renamed bits, times one blind to them, as the letter
on the first factor. -/
private theorem letterAmp_renameBits {N m : ℕ} {ι : Fin n → Fin N} (hι : Function.Injective ι)
    (G : GateLetter n m) (f : (Fin n → ZMod 2) → ℂ) (g : (Fin N → ZMod 2) → ℂ)
    (hg : ∀ w k v, g (Function.update w (ι k) v) = g w) :
    letterAmp (G.renameBits ι hι) (fun w => f (w ∘ ι) * g w)
      = fun w => letterAmp G f (w ∘ ι) * g w := by
  funext w
  cases G with
  | hadamard k =>
    change walshTransform (ι k) (fun w => f (w ∘ ι) * g w) w = walshTransform k f (w ∘ ι) * g w
    simp only [walshTransform, hg, Function.update_comp_eq_of_injective w hι, Function.comp_apply]
    ring
  | diagonal D =>
    change charOf m (DiagPhase.eval (MvPolynomial.rename ι D) w) * (f (w ∘ ι) * g w)
      = charOf m (DiagPhase.eval D (w ∘ ι)) * f (w ∘ ι) * g w
    have he : DiagPhase.eval (MvPolynomial.rename ι D) w = DiagPhase.eval D (w ∘ ι) := by
      unfold DiagPhase.eval
      rw [MvPolynomial.eval_rename]
      rfl
    rw [he, mul_assoc]
  | cnot i j hij =>
    change f (DiagPhase.cnotBitMap (ι i) (ι j) w ∘ ι) * g (DiagPhase.cnotBitMap (ι i) (ι j) w)
      = f (DiagPhase.cnotBitMap i j (w ∘ ι)) * g w
    unfold DiagPhase.cnotBitMap
    rw [hg, Function.update_comp_eq_of_injective w hι]
    rfl

/-- A renamed word acts on a function of the renamed bits, times one blind to them, as the word on
the first factor. -/
private theorem runAmp_map_renameBits {N m : ℕ} {ι : Fin n → Fin N} (hι : Function.Injective ι)
    (W : GateWord n m) (f : (Fin n → ZMod 2) → ℂ) (g : (Fin N → ZMod 2) → ℂ)
    (hg : ∀ w k v, g (Function.update w (ι k) v) = g w) :
    runAmp (W.map (GateLetter.renameBits ι hι)) (fun w => f (w ∘ ι) * g w)
      = fun w => runAmp W f (w ∘ ι) * g w := by
  induction W generalizing f with
  | nil => rfl
  | cons G W ih =>
    rw [List.map_cons, runAmp_cons, runAmp_cons, letterAmp_renameBits hι G f g hg, ih]

/-- Two blocks' bits are distinct on the register. -/
private theorem Register.bit_ne {b : ℕ} (R : Register b) {s t : Fin b} (hst : s ≠ t)
    (x : Fin (R.blockSize s)) (k : Fin (R.blockSize t)) : R.bit s x ≠ R.bit t k :=
  fun h => hst (congrArg Sigma.fst (finSigmaFinEquiv.injective h))

/-- One block's renamed word on a blockwise product acts on that block's factor alone. -/
private theorem Register.runAmp_block {b : ℕ} (R : Register b) {m : ℕ} (t : Fin b)
    (W : GateWord (R.blockSize t) m) (F : (s : Fin b) → (Fin (R.blockSize s) → ZMod 2) → ℂ) :
    runAmp (W.map (GateLetter.renameBits (R.bit t) (R.bit_injective t)))
        (fun w => ∏ s, F s (w ∘ R.bit s))
      = fun w => ∏ s, Function.update F t (runAmp W (F t)) s (w ∘ R.bit s) := by
  have hsplit : ∀ (G : (s : Fin b) → (Fin (R.blockSize s) → ZMod 2) → ℂ)
      (w : Fin R.totalBits → ZMod 2),
      ∏ s, G s (w ∘ R.bit s) = G t (w ∘ R.bit t) * ∏ s ∈ Finset.univ.erase t, G s (w ∘ R.bit s) :=
    fun G w => (Finset.mul_prod_erase _ (fun s => G s (w ∘ R.bit s)) (Finset.mem_univ t)).symm
  have hg : ∀ (w : Fin R.totalBits → ZMod 2) (k : Fin (R.blockSize t)) (v : ZMod 2),
      ∏ s ∈ Finset.univ.erase t, F s (Function.update w (R.bit t k) v ∘ R.bit s)
        = ∏ s ∈ Finset.univ.erase t, F s (w ∘ R.bit s) := fun w k v =>
    Finset.prod_congr rfl fun s hs => by
      rw [Function.update_comp_eq_of_forall_ne w v fun x =>
        R.bit_ne (Finset.ne_of_mem_erase hs) x k]
  rw [show (fun w => ∏ s, F s (w ∘ R.bit s))
      = fun w => F t (w ∘ R.bit t) * ∏ s ∈ Finset.univ.erase t, F s (w ∘ R.bit s) from
    funext (hsplit F), runAmp_map_renameBits (R.bit_injective t) W (F t) _ hg]
  funext w
  rw [hsplit, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]

/-- The blocks of a duplicate-free list, their renamed words concatenated, on a blockwise product
act block by block. -/
private theorem Register.runAmp_flatMap {b : ℕ} (R : Register b) {m : ℕ}
    (ws : (t : Fin b) → GateWord (R.blockSize t) m) :
    ∀ l : List (Fin b), l.Nodup → ∀ F : (s : Fin b) → (Fin (R.blockSize s) → ZMod 2) → ℂ,
      runAmp (l.flatMap fun t => (ws t).map (GateLetter.renameBits (R.bit t) (R.bit_injective t)))
          (fun w => ∏ s, F s (w ∘ R.bit s))
        = fun w => ∏ s, (if s ∈ l then runAmp (ws s) (F s) else F s) (w ∘ R.bit s)
  | [], _, F => by
    rw [List.flatMap_nil, runAmp_nil]
    funext w
    exact Finset.prod_congr rfl fun s _ => by rw [if_neg List.not_mem_nil]
  | t :: l, hl, F => by
    rw [List.flatMap_cons, runAmp_append, R.runAmp_block t (ws t) F,
      R.runAmp_flatMap ws l (List.nodup_cons.mp hl).2]
    have hG : ∀ s, (if s ∈ l then runAmp (ws s) (Function.update F t (runAmp (ws t) (F t)) s)
          else Function.update F t (runAmp (ws t) (F t)) s)
        = if s ∈ t :: l then runAmp (ws s) (F s) else F s := by
      intro s
      by_cases hs : s = t
      · subst hs
        rw [if_neg (List.nodup_cons.mp hl).1, if_pos List.mem_cons_self, Function.update_self]
      · rw [Function.update_of_ne hs]
        simp only [List.mem_cons, hs, false_or]
    funext w
    exact Finset.prod_congr rfl fun s _ => by rw [hG s]

/-- **The blockwise word on a blockwise product** acts block by block. -/
private theorem Register.runAmp_word {b : ℕ} (R : Register b) {m : ℕ}
    (ws : (t : Fin b) → GateWord (R.blockSize t) m)
    (F : (s : Fin b) → (Fin (R.blockSize s) → ZMod 2) → ℂ) :
    runAmp (R.word ws) (fun w => ∏ s, F s (w ∘ R.bit s))
      = fun w => ∏ s, runAmp (ws s) (F s) (w ∘ R.bit s) := by
  rw [Register.word, R.runAmp_flatMap ws _ (List.nodup_finRange b)]
  simp only [List.mem_finRange, if_true]

/-- **The amplitude of states appended in order** is the product of their amplitudes, each read
on its own block. -/
private theorem amp_appendStates : ∀ {b : ℕ} {N : Fin b → ℕ}
    (F : (t : Fin b) → KernelSumState (N t)) (w : Fin (∑ t, N t) → ZMod 2),
    amp (appendStates F) w = ∏ t, amp (F t) (fun j => w (finSigmaFinEquiv ⟨t, j⟩))
  | 0, _, _, w => by
    change amp (castBits _ (idState 0)) w = _
    rw [amp_castBits, amp_idState]
    beta_reduce
    rw [if_pos (funext fun i => Fin.elim0 i)]
    exact (Finset.prod_of_isEmpty _).symm
  | b + 1, N, F, w => by
    change amp (castBits _ (appendState (appendStates fun t => F (Fin.castSucc t))
      (F (Fin.last b)))) w = _
    rw [amp_castBits, amp_appendState]
    beta_reduce
    rw [Fin.prod_univ_castSucc, amp_appendStates (fun t => F (Fin.castSucc t))]
    congr 1
    · refine Finset.prod_congr rfl fun t _ => congrArg (amp (F _)) (funext fun j => ?_)
      simp only [Function.comp_apply]
      congr 1
      ext
      simp only [Fin.val_cast, Fin.val_castAdd, finSigmaFinEquiv_apply]
      rfl
    · refine congrArg (amp (F _)) (funext fun j => ?_)
      simp only [Function.comp_apply]
      congr 1
      ext
      simp only [Fin.val_cast, Fin.val_natAdd, finSigmaFinEquiv_apply]
      rfl

/-- States appended in order are a carrier state when each is. -/
private theorem isCarrier_appendStates : ∀ {b : ℕ} {N : Fin b → ℕ}
    {F : (t : Fin b) → KernelSumState (N t)}, (∀ t, IsCarrier (F t)) → IsCarrier (appendStates F)
  | 0, _, _, _ => isCarrier_castBits _ (isCarrier_idState 0)
  | _ + 1, _, _, hF =>
    isCarrier_castBits _ (isCarrier_appendState (isCarrier_appendStates fun _ => hF _) (hF _))

/-- States appended in order, each at a positive precision `m`, are at precision at most `m`, and
at `m` when there is at least one. -/
private theorem appendStates_m : ∀ {b : ℕ} {N : Fin b → ℕ}
    (F : (t : Fin b) → KernelSumState (N t)) {m : ℕ}, 1 ≤ m → (∀ t, (F t).m = m) →
    (appendStates F).m ≤ m ∧ (0 < b → (appendStates F).m = m)
  | 0, _, _, _, hm1, _ => ⟨hm1, fun h => absurd h (lt_irrefl 0)⟩
  | _ + 1, _, F, m, hm1, hm => by
    have he : (appendStates F).m = m := by
      change (castBits _ (appendState (appendStates fun t => F (Fin.castSucc t))
        (F (Fin.last _)))).m = m
      rw [StabCode.castBits_m]
      change max _ (F _).m = m
      rw [hm, max_eq_right (appendStates_m (fun t => F (Fin.castSucc t)) hm1 fun t => hm _).1]
    exact ⟨he.le, fun _ => he⟩

/-- A reindexing keeps the precision. -/
private theorem reindexFreeBits_m {N N' : ℕ} (h : N = N') (e : Fin N ≃ Fin N')
    (S : KernelSumState N) : (reindexFreeBits h e S).m = S.m := by
  subst h
  rfl

/-- The layout takes block `t`'s `i`-th logical input bit to that block's `i`-th logical bit. -/
private theorem Register.layout_logical {b : ℕ} (R : Register b) (t : Fin b)
    (i : Fin (R.blockSize t - R.generatorCount t)) :
    R.layout (Fin.castAdd R.ancillaCount
        (finSigmaFinEquiv (n := fun t => R.blockSize t - R.generatorCount t) ⟨t, i⟩))
      = R.bit t ((R.code t).logicalBit i) := by
  simp only [Register.layout, Register.bit, StabCode.logicalBit, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_apply_apply,
    Equiv.sigmaSumDistrib_symm_apply, Equiv.sigmaCongrRight_apply, finCongr_apply]
  rfl

/-- The layout takes block `t`'s `j`-th ancilla of the input to that block's `j`-th ancilla. -/
private theorem Register.layout_ancilla {b : ℕ} (R : Register b) (t : Fin b)
    (j : Fin (R.generatorCount t)) :
    R.layout (Fin.natAdd R.logicalCount (finSigmaFinEquiv (n := R.generatorCount) ⟨t, j⟩))
      = R.bit t ((R.code t).ancillaBit j) := by
  simp only [Register.layout, Register.bit, StabCode.ancillaBit, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_apply_apply,
    Equiv.sigmaSumDistrib_symm_apply, Equiv.sigmaCongrRight_apply, finCongr_apply]
  rfl

/-- The register's ancillas, read through the layout, are every block's ancillas. -/
private theorem Register.ancillas_zero_iff {b : ℕ} (R : Register b)
    (w : Fin R.totalBits → ZMod 2) :
    (∀ i : Fin (R.logicalCount + R.ancillaCount), R.logicalCount ≤ i.val → w (R.layout i) = 0)
      ↔ ∀ t, ∀ i : Fin (R.blockSize t), R.blockSize t - R.generatorCount t ≤ i.val →
          w (R.bit t i) = 0 := by
  constructor
  · intro hA t i hi
    have hr := (R.code t).r_le
    have hlt : i.val - (R.blockSize t - R.generatorCount t) < R.generatorCount t := by omega
    have hi' : i = (R.code t).ancillaBit ⟨i.val - (R.blockSize t - R.generatorCount t), hlt⟩ := by
      apply Fin.ext
      simp only [StabCode.ancillaBit, Fin.val_cast, Fin.val_natAdd]
      omega
    rw [hi', ← R.layout_ancilla]
    exact hA _ (Nat.le_add_right _ _)
  · intro hB i hi
    have hlt : i.val - R.logicalCount < R.ancillaCount := by omega
    have hi' : i = Fin.natAdd R.logicalCount
        (finSigmaFinEquiv (n := R.generatorCount)
          (finSigmaFinEquiv.symm ⟨i.val - R.logicalCount, hlt⟩)) := by
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    rw [hi']
    obtain ⟨t, j⟩ := finSigmaFinEquiv.symm (⟨i.val - R.logicalCount, hlt⟩ : Fin R.ancillaCount)
    rw [R.layout_ancilla]
    refine hB t _ ?_
    simp only [StabCode.ancillaBit, Fin.val_cast, Fin.val_natAdd]
    omega

/-- **The register's input on a product** is the blocks' inputs, each with its ancillas padded
with zeros, multiplied block by block. -/
private theorem Register.amp_input_appendStates {b : ℕ} (R : Register b)
    (S : (t : Fin b) → KernelSumState (R.blockSize t - R.generatorCount t))
    (hX : IsCarrier (appendStates S)) :
    amp (R.input (appendStates S))
      = fun w => ∏ t, padZero (Nat.sub_le _ _) (amp (S t)) (w ∘ R.bit t) := by
  funext w
  rw [Register.input, amp_reindexFreeBits, amp_pinZeros _ hX]
  unfold padZero
  rw [Fintype.prod_ite_zero]
  simp only [Function.comp_apply]
  rw [amp_appendStates]
  refine if_congr (R.ancillas_zero_iff w) (Finset.prod_congr rfl fun t _ => ?_) rfl
  exact congrArg (amp (S t)) (funext fun j => congrArg w (R.layout_logical t j))

/-- **The blockwise encoder on a product input**: on the blocks' carrier inputs at the words'
precision, appended, the blockwise encoding is `StateEq` to the blocks' encodings appended. Any
words, encoders or not. -/
theorem blockEncode_appendState {b : ℕ} (R : Register b) {m : ℕ}
    (ws : (t : Fin b) → GateWord (R.blockSize t) m)
    (S : (t : Fin b) → KernelSumState (R.blockSize t - R.generatorCount t))
    (hS : ∀ t, IsCarrier (S t)) (hm : ∀ t, (S t).m = m) :
    StateEq (R.blockEncode ws (appendStates S))
      (appendStates fun t => (R.code t).encode (ws t) (S t)) := by
  have hX : IsCarrier (appendStates S) := isCarrier_appendStates hS
  have hrun : amp (R.blockEncode ws (appendStates S))
      = runAmp (R.word ws) (amp (R.input (appendStates S))) := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      have hw : R.word ws = [] := by
        change (List.finRange 0).flatMap _ = []
        rw [List.finRange_zero, List.flatMap_nil]
      rw [Register.blockEncode, hw, run_nil, runAmp_nil]
    · have hm1 : 1 ≤ m := hm ⟨0, hb⟩ ▸ (hS ⟨0, hb⟩).1
      have hXm := (appendStates_m S hm1 hm).2 hb
      obtain ⟨hP, hPm, -⟩ := StabCode.pinZeros_spec R.ancillaCount hX
      exact amp_run _ (isCarrier_reindexFreeBits _ _ hP)
        ((reindexFreeBits_m _ _ _).trans (hPm.trans hXm))
  unfold StateEq
  rw [hrun, R.amp_input_appendStates S hX]
  refine (R.runAmp_word ws (fun t => padZero (Nat.sub_le _ _) (amp (S t)))).trans ?_
  funext w
  rw [amp_appendStates]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [(isCarrier_encode (R.code t) (ws t) (hS t) (hm t)).2]
  rfl

end FTQCLib.Frame.Walkthrough

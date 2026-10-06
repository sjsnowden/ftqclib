/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.CarrierScale
import FTQCLib.Bridge.HOFBridge

/-!
# Injecting any diagonal gate as a protocol

The injection of a diagonal gate (`docs/TARGETS.md`, T22) is a protocol of T14 (`Protocol.lean`).
Its data are: a precision `m`; a **phase polynomial** `f : DiagPhase k m` on `k` qubits, any
polynomial with coefficients in `ZMod (2^m)`, whose gate `ζ^f` multiplies the word `y` by
`ζ^{f(y)}` with `ζ = exp(2πi/2^m)` (`charOf m`); an arbitrary carrier register `S` on `n` free bits,
at any height and any precision `S.m ≤ m`; and the **chosen data qubits** `q : Fin k → Fin n`, any
map, so that `ζ^f` acts on the register as the diagonal gate `x ↦ ζ^{f(x ∘ q)}`, whose exponent is
`rename q f` (T05's diagonal letter on the register's bits).

**The input** (`diagonalInjectionInput`). The register is lifted to precision `m` by R7
(`liftPrecision`), `k` ancillas are appended as `∣0⟩ + ∣1⟩` each (`appendFreeBits`: the ancilla `i`
is free bit `n + i`), and the diagonal letter `f` on the ancillas makes them the magic state
`ζ^f ∣+⟩^{⊗k}`. The input is the register beside the magic state, on `n + k` free bits.

**The protocol** (`diagonalInjectionProtocol`, a `Protocol m (n + k) k`):

1. a CNOT from each chosen data qubit `q i` to its ancilla `n + i` (`ancillaCnotWord`);
2. the Z-measurement of each ancilla `i`, in the order `i = 0, …, k − 1`, a conditioning letter on
   `Z_{n+i}` with sign `+`, whose outcome is the new free bit `n + k + i` (decision D2 as revised):
   the outcome string `c : Fin k → ZMod 2` is read at those bits (`measureAncillas`);
3. the correction, one diagonal letter on the data and outcome free bits (T13's feed-forward), with
   exponent `f(x ∘ q) − f(x ∘ q ⊕ c)` (`correctionPhase`; `correctionPhase_eval`). It does not
   read the ancillas.

**A branch, processed** (`diagonalInjectionBranch`). The outcome bits of the protocol's one carrier
state are evaluated at `c` and dropped (`restrictLast`, `k` uses of `restrictZ`, T12, whose
amplitude is the evaluation), which reads the protocol's branch as a carrier state on the
register and the ancillas. Each ancilla `i` was measured into `c i`, so it is then dropped at `c i`
by `restrictLast` again. The result is a carrier state on the register's `n` bits.

**The statement** (`diagonalInjection_correct`). For every carrier state `S`, every precision
`m ≥ S.m`, every phase polynomial `f` on `k` qubits at precision `m`, every map `q` choosing the
data qubits, and every outcome string `c`:

* the protocol's branch at `c` (T14's `branchWeight`) has weight `2^{−k}` of the input's
  `ampNormSq`;
* the processed branch has weight `2^{−k}` of the input's;
* it is a carrier state;
* it is `StateEq` to `ζ^f` applied to the register, T05's run of the one diagonal letter
  `rename q f` on the lifted register (decision D8);
* it is related to that output by T07's rules (`Relation.EqvGen CarrierRule`).

**The correction's degree** (`correction_degree_lt`). In the branch at `c` the correction's
exponent, as a function of the register's and the ancillas' bits, is `x ↦ f(x ∘ q) − f(x ∘ q + c)`:
minus the difference of `f` in the direction `c`, read through `q`. So its nonclassical degree
(`IsPolyDegLE`, ECCLib) is one below `f`'s: if `f` has degree at most `d + 1`, the correction has
degree at most `d`; for a multilinear `f`, whose degree is at most its `effectiveLevel`
(`eval_isPolyDegLE_effectiveLevel`), the correction's is at most `effectiveLevel f − 1`. The degree
is that of each branch's correction, at a fixed outcome string, and not of the exponent as a
function of the outcome bits too: for T at `m = 3` the exponent on data and outcome bits is
`2xc − c`, whose degree is three, while at `c = 1` it is `2x − 1`, an S, of degree two.

**Reading of "the input's weight".** As in `HInject.lean`: the input is the register with its
ancillas, and `appendFreeBits` keeps the scale (D3), so each ancilla is `∣0⟩ + ∣1⟩ = √2·∣+⟩` and the
magic state's letter has modulus one. The input's weight is `2^k` times the register's, and each
branch's weight `2^{−k}` of the input's is the register's own, as `ζ^f` keeps `Σ_w |·|²`. The
weight clause and the clause `StateEq` to `ζ^f`'s output hold together only so.

**Frame form** (decision D5). The gate `ζ^f` is T05's diagonal letter, whose referee is
multiplication by `charOf m (f(x ∘ q))`; the magic state is the register beside that letter's run
on `|+⟩^{⊗k}`; the Z-measurement is T10's projection `½(1 + (−1)^b Z)` with the outcome as a free
bit. No `FTQCLib.Hilbert` module is imported.

## Main definitions

* `diagonalInjectionInput` — the register lifted to precision `m`, beside the magic state
  `ζ^f ∣+⟩^{⊗k}` on `k` ancillas.
* `ancillaCnotWord`, `measureAncillas`, `correctionPhase` — the CNOTs, the Z-measurements of the
  ancillas, and the correction's exponent.
* `diagonalInjectionProtocol` — the protocol.
* `diagonalInjectionBranch` — the branch of an outcome string as a carrier state on the register.

## Main results

* `correctionPhase_eval` — the correction's exponent is `f(x ∘ q) − f(x ∘ q ⊕ c)`.
* `diagonalInjectionInput_spec`, `amp_run_diagonal_rename` — the input and the gate's output as
  carrier states, with their amplitudes.
* `restrictLast_restrictLast_interpret_spec` — a processed branch of any protocol with `k` outcome
  bits on `n + k` free bits, from its referee.
* `diagonalInjection_correct` — each branch has weight `2^{−k}` of the input's, is a carrier state,
  is `StateEq` to `ζ^f` applied to the input, and is related to it by T07's rules (proved at
  T22.3.1).
* `correction_degree_lt` — the correction's nonclassical degree is one below `f`'s (proved at
  T22.3.2).

## Implementation notes

* The register is lifted to the gate's precision `m` (R7, `liftPrecision`), as in `RemoteCH.lean`:
  a diagonal letter at precision `m` acts only on a state at precision `m`. T at `m = 3`, CS at
  `m = 2`, CCZ at `m = 1` and `√T` at `m = 4` are the instances `f = X₀`, `f = X₀X₁`, `f = X₀X₁X₂`
  and `f = X₀`, each at its own `m`.
* `q` is any map. The CNOTs have distinct targets, the ancillas, and their controls are data bits,
  which no letter changes, so two chosen qubits may coincide; the gate is then `ζ^f` read through
  `q`, which is still `rename q f`.
* The Z-measurement needs no precision above `m`: `Z` has no Y (`signedZ_side`).
* Exclusive or on bits is the polynomial `a + b − 2ab` over `ZMod (2^m)`: on `0` and `1` it is
  `a ⊕ b`. The correction is `bind₁` of `f` at the data bits, minus `bind₁` of `f` at their
  exclusive or with the outcome bits.
* `restrictLast` (`ConditionFloor.lean`) drops the last bit first, so the bit `n + i` is read at
  `c i`, as T14's branch reads the outcome string at `Fin.append w c`. `appendFreeBits` and
  `restrictLast`, the carrier facts about them, the scale (`CarrierScale.lean`) and the degree
  lemmas (`ECCLib/Polynomial.lean`) are public in their own modules (docs/STEPS.md, entry
  2026-10-01g).

## References

* X. Zhou, D. W. Leung and I. L. Chuang, *Methodology for quantum logic gate construction*,
  arXiv:quant-ph/0002039: one-bit teleportation, and its recursive construction of the diagonal
  gates of every level of the hierarchy; cited unit by unit above the declarations.
* D. Gottesman and I. L. Chuang, *Quantum teleportation is a universal computational primitive*,
  arXiv:quant-ph/9908010: a gate of level `k` performed by teleportation with a correction of level
  `k − 1`; cited above `diagonalInjection_correct` and `correction_degree_lt`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer ECCLib

variable {n : ℕ}

/-! ## The input: the register beside the magic state -/

-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:basic2
/-- **The input**: the register `S` lifted to the gate's precision `m` (R7), `k` ancillas appended
as `∣0⟩ + ∣1⟩` each (bits `n + i`), and the diagonal letter `f` on the ancillas, which makes them
the magic state `ζ^f ∣+⟩^{⊗k}`. -/
noncomputable def diagonalInjectionInput {m k : ℕ} (f : DiagPhase k m) (S : KernelSumState n)
    (hmk : S.m ≤ m) : KernelSumState (n + k) :=
  run ([GateLetter.diagonal (MvPolynomial.rename (Fin.natAdd n) f)] : GateWord (n + k) m)
    (appendFreeBits k (liftPrecision S m hmk))

/-! ## The protocol -/

/-- A data bit is not an ancilla. -/
private theorem castAdd_ne_natAdd_diagonalInjection {k : ℕ} (i : Fin n) (j : Fin k) :
    Fin.castAdd k i ≠ Fin.natAdd n j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

/-- **The CNOTs**: from each chosen data qubit `q i` to its ancilla, bit `n + i`. -/
def ancillaCnotWord {m k : ℕ} (q : Fin k → Fin n) : GateWord (n + k) m :=
  List.ofFn fun i =>
    GateLetter.cnot (Fin.castAdd k (q i)) (Fin.natAdd n i)
      (castAdd_ne_natAdd_diagonalInjection (q i) i)

/-- **The CNOTs, then the Z-measurements of the first `j` ancillas**, in order: the `i`-th
conditioning letter measures `Z` on the ancilla `n + i`, and its outcome is the new free bit
`n + k + i`. -/
noncomputable def measureAncillas {m k : ℕ} (q : Fin k → Fin n) :
    (j : ℕ) → j ≤ k → Protocol m (n + k) j
  | 0, _ => Protocol.nil.word (ancillaCnotWord (n := n) (k := k) q : GateWord (n + k) m)
  | j + 1, h =>
    (measureAncillas q j (Nat.le_of_succ_le h)).condition
      (signedZ (Fin.castAdd j (Fin.natAdd n ⟨j, h⟩))) (signedZ_side _)

/-- **The correction's exponent**, on the data, ancilla and outcome bits: `f` at the chosen data
qubits, minus `f` at their exclusive or with the outcome bits, the exclusive or of bits `a`, `b`
written `a + b − 2ab`. It reads no ancilla. -/
noncomputable def correctionPhase {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m) :
    DiagPhase (n + k + k) m :=
  let x : Fin k → DiagPhase (n + k + k) m :=
    fun i => MvPolynomial.X (Fin.castAdd k (Fin.castAdd k (q i)))
  let c : Fin k → DiagPhase (n + k + k) m := fun i => MvPolynomial.X (Fin.natAdd (n + k) i)
  MvPolynomial.bind₁ x f - MvPolynomial.bind₁ (fun i => x i + c i - 2 * x i * c i) f

-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:basic1
-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:basic2
/-- **The injection of `ζ^f`** at precision `m` on the chosen data qubits `q`, on the register's
`n` bits and the `k` ancillas: a CNOT from each `q i` to its ancilla; the Z-measurement of each
ancilla `i`, its outcome the new free bit `n + k + i`; then the correction, one diagonal letter on
the data and outcome bits with exponent `f(x ∘ q) − f(x ∘ q ⊕ c)`. -/
noncomputable def diagonalInjectionProtocol {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m) :
    Protocol m (n + k) k :=
  (measureAncillas q k le_rfl).word [GateLetter.diagonal (correctionPhase q f)]

/-! ## A branch, processed -/

/-- **The branch of the outcome string `c`, processed**, on the register's `n` bits: the protocol
run on its input; the outcome bits evaluated at `c` and dropped (`restrictLast`), which reads the
protocol's branch as a carrier state; then each ancilla `i` dropped at `c i`, the bit its
measurement left it at. -/
noncomputable def diagonalInjectionBranch {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    (S : KernelSumState n) (hmk : S.m ≤ m) (c : Fin k → ZMod 2) : KernelSumState n :=
  restrictLast k c
    (restrictLast k c ((diagonalInjectionProtocol q f).interpret (diagonalInjectionInput f S hmk)))

/-! ## The correction's exponent -/

/-- Exclusive or of two bits, `a + b − 2ab` over `ZMod (2^m)`, is their sum in `ZMod 2`. -/
private theorem xor_val_diagonalInjection (m : ℕ) (a b : ZMod 2) :
    ((a.val : ZMod (2 ^ m)) + (b.val : ZMod (2 ^ m)) - 2 * (a.val : ZMod (2 ^ m)) * b.val)
      = ((a + b).val : ZMod (2 ^ m)) := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp only [ZMod.val_zero, show (1 : ZMod 2).val = 1 from rfl,
      show (1 + 1 : ZMod 2) = 0 from rfl, zero_add, add_zero, Nat.cast_zero, Nat.cast_one] <;>
    ring

/-- **The correction's exponent** at the word `w` of the data, ancilla and outcome bits is
`f(x ∘ q) − f(x ∘ q ⊕ c)`, where `x ∘ q` is `w` at the chosen data qubits and `c` is `w` at the
outcome bits. -/
theorem correctionPhase_eval {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    (w : Fin (n + k + k) → ZMod 2) :
    (correctionPhase q f).eval w
      = f.eval (fun i => w (Fin.castAdd k (Fin.castAdd k (q i))))
        - f.eval (fun i => w (Fin.castAdd k (Fin.castAdd k (q i))) + w (Fin.natAdd (n + k) i)) := by
  have hbind : ∀ g : Fin k → DiagPhase (n + k + k) m,
      MvPolynomial.eval (DiagPhase.liftBinary w) (MvPolynomial.bind₁ g f)
        = MvPolynomial.eval (fun i => MvPolynomial.eval (DiagPhase.liftBinary w) (g i)) f :=
    fun g => MvPolynomial.eval₂Hom_bind₁ (RingHom.id _) _ g f
  have hx : (fun i => MvPolynomial.eval (DiagPhase.liftBinary w)
      (MvPolynomial.X (Fin.castAdd k (Fin.castAdd k (q i))) : DiagPhase (n + k + k) m))
        = DiagPhase.liftBinary (m := m) fun i => w (Fin.castAdd k (Fin.castAdd k (q i))) := by
    funext i
    simp only [MvPolynomial.eval_X, DiagPhase.liftBinary]
  have hxc : (fun i => MvPolynomial.eval (DiagPhase.liftBinary w)
      ((MvPolynomial.X (Fin.castAdd k (Fin.castAdd k (q i))) : DiagPhase (n + k + k) m)
        + MvPolynomial.X (Fin.natAdd (n + k) i)
        - 2 * MvPolynomial.X (Fin.castAdd k (Fin.castAdd k (q i)))
          * MvPolynomial.X (Fin.natAdd (n + k) i)))
        = DiagPhase.liftBinary (m := m) fun i =>
          w (Fin.castAdd k (Fin.castAdd k (q i))) + w (Fin.natAdd (n + k) i) := by
    funext i
    simp only [map_sub, map_add, map_mul, MvPolynomial.eval_X, map_ofNat, DiagPhase.liftBinary]
    exact xor_val_diagonalInjection m _ _
  simp only [correctionPhase, DiagPhase.eval]
  rw [map_sub, hbind, hbind, hx, hxc]

/-! ## The referee in closed form -/

/-- **The input**: a carrier state at precision `m`, whose amplitude at the word `u` of the
register's and the ancillas' bits is `ζ^{f(a)}` times the register's at `x`, `x` and `a` the
register's and the ancillas' parts of `u`. -/
theorem diagonalInjectionInput_spec {m k : ℕ} (f : DiagPhase k m) {S : KernelSumState n}
    (hS : IsCarrier S) (hmk : S.m ≤ m) :
    IsCarrier (diagonalInjectionInput f S hmk) ∧ (diagonalInjectionInput f S hmk).m = m ∧
      amp (diagonalInjectionInput f S hmk) = fun u =>
        charOf m (f.eval fun i => u (Fin.natAdd n i)) * amp S (fun i => u (Fin.castAdd k i)) := by
  have hA := isCarrier_appendFreeBits k (isCarrier_liftPrecision hS m hmk)
  have hAm : (appendFreeBits k (liftPrecision S m hmk)).m = m := (appendFreeBits_m k _).trans rfl
  refine ⟨isCarrier_run _ hA hAm, (run_m _ _).trans hAm, ?_⟩
  unfold diagonalInjectionInput
  rw [amp_run _ hA hAm, amp_appendFreeBits, amp_liftPrecision]
  funext u
  simp only [runAmp_cons, runAmp_nil, letterAmp, DiagPhase.eval_rename]
  rfl

/-- Two different ancillas are different bits. -/
private theorem natAdd_ne_diagonalInjection {k : ℕ} {i j : Fin k} (h : i ≠ j) :
    (Fin.natAdd n i : Fin (n + k)) ≠ Fin.natAdd n j := by
  intro e
  apply h
  have hv := congrArg Fin.val e
  simp only [Fin.val_natAdd] at hv
  exact Fin.ext (by omega)

/-- **A list of the CNOTs**, each from a chosen data qubit to its ancilla, precomposes the
amplitude with the word that adds to each ancilla `i` its data qubit `q i`, as many times as `i`
occurs in the list. The data bits are unchanged. -/
private theorem runAmp_map_cnot {m k : ℕ} (q : Fin k → Fin n) (l : List (Fin k))
    (F : (Fin (n + k) → ZMod 2) → ℂ) (w : Fin (n + k) → ZMod 2) :
    ∃ v : Fin (n + k) → ZMod 2, (∀ i, v (Fin.castAdd k i) = w (Fin.castAdd k i)) ∧
      (∀ i, v (Fin.natAdd n i)
        = w (Fin.natAdd n i) + (l.count i : ZMod 2) * w (Fin.castAdd k (q i))) ∧
      runAmp (l.map fun i => (GateLetter.cnot (Fin.castAdd k (q i)) (Fin.natAdd n i)
        (castAdd_ne_natAdd_diagonalInjection (q i) i) : GateLetter (n + k) m)) F w = F v := by
  induction l generalizing F with
  | nil =>
    refine ⟨w, fun _ => rfl, fun i => ?_, rfl⟩
    rw [List.count_nil, Nat.cast_zero, zero_mul, add_zero]
  | cons i₀ l ih =>
    obtain ⟨v, hv1, hv2, hv3⟩ := ih (letterAmp (GateLetter.cnot (Fin.castAdd k (q i₀))
      (Fin.natAdd n i₀) (castAdd_ne_natAdd_diagonalInjection (q i₀) i₀) : GateLetter (n + k) m) F)
    refine ⟨DiagPhase.cnotBitMap (Fin.castAdd k (q i₀)) (Fin.natAdd n i₀) v, fun i => ?_,
      fun i => ?_, ?_⟩
    · unfold DiagPhase.cnotBitMap
      rw [Function.update_of_ne (castAdd_ne_natAdd_diagonalInjection i i₀), hv1]
    · unfold DiagPhase.cnotBitMap
      by_cases h : i = i₀
      · subst h
        rw [Function.update_self, hv2, hv1, List.count_cons_self]
        push_cast
        ring
      · rw [Function.update_of_ne (natAdd_ne_diagonalInjection h), hv2,
          List.count_cons_of_ne (Ne.symm h)]
    · rw [List.map_cons, runAmp_cons, hv3]
      rfl

/-- **The amplitude after the CNOTs**: `ζ^{f(a ⊕ x ∘ q)}` times the register's at `x`. -/
private noncomputable def injectAmp {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    (s : (Fin n → ZMod 2) → ℂ) (u : Fin (n + k) → ZMod 2) : ℂ :=
  charOf m (f.eval fun i => u (Fin.natAdd n i) + u (Fin.castAdd k (q i)))
    * s (fun i => u (Fin.castAdd k i))

/-- The CNOTs turn the input's amplitude into `injectAmp`. -/
private theorem runAmp_ancillaCnotWord {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    (s : (Fin n → ZMod 2) → ℂ) (u : Fin (n + k) → ZMod 2) :
    runAmp (ancillaCnotWord (m := m) q)
        (fun u => charOf m (f.eval fun i => u (Fin.natAdd n i)) * s (fun i => u (Fin.castAdd k i)))
        u
      = injectAmp q f s u := by
  obtain ⟨v, hv1, hv2, hv3⟩ := runAmp_map_cnot (m := m) q (List.finRange k)
    (fun u => charOf m (f.eval fun i => u (Fin.natAdd n i)) * s (fun i => u (Fin.castAdd k i))) u
  unfold ancillaCnotWord
  rw [List.ofFn_eq_map, hv3]
  have h1 : (fun i => v (Fin.castAdd k i)) = fun i => u (Fin.castAdd k i) := funext hv1
  have h2 : (fun i => v (Fin.natAdd n i))
      = fun i => u (Fin.natAdd n i) + u (Fin.castAdd k (q i)) := by
    funext i
    rw [hv2, List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange i), Nat.cast_one,
      one_mul]
  change charOf m (f.eval fun i => v (Fin.natAdd n i)) * s (fun i => v (Fin.castAdd k i)) = _
  rw [h1, h2]
  rfl

/-- **The referee after the CNOTs and the first `j` Z-measurements**: `injectAmp` on the
register's and the ancillas' bits where each measured ancilla equals its outcome bit, and zero
elsewhere. -/
private theorem interpretAmp_measureAncillas {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    (s : (Fin n → ZMod 2) → ℂ) :
    ∀ (j : ℕ) (h : j ≤ k) (v : Fin (n + k + j) → ZMod 2),
      (measureAncillas (m := m) q j h).interpretAmp
          (fun u => charOf m (f.eval fun i => u (Fin.natAdd n i))
            * s (fun i => u (Fin.castAdd k i))) v
        = if ∀ i : Fin j,
            v (Fin.castAdd j (Fin.natAdd n (Fin.castLE h i))) = v (Fin.natAdd (n + k) i)
          then injectAmp q f s (fun t => v (Fin.castAdd j t)) else 0
  | 0, h, v => by
    rw [if_pos (fun i => i.elim0)]
    exact runAmp_ancillaCnotWord q f s v
  | j + 1, h, v => by
    have hj : j ≤ k := Nat.le_of_succ_le h
    change pauliProjection (signedZ (Fin.castAdd j (Fin.natAdd n ⟨j, h⟩)))
      (v (Fin.last (n + k + j)))
      ((measureAncillas (m := m) q j hj).interpretAmp
        (fun u => charOf m (f.eval fun i => u (Fin.natAdd n i))
          * s (fun i => u (Fin.castAdd k i)))) (Fin.init v) = _
    rw [pauliProjection_signedZ,
      interpretAmp_measureAncillas q f s j hj (Fin.init v)]
    have hiff : (∀ i : Fin (j + 1),
        v (Fin.castAdd (j + 1) (Fin.natAdd n (Fin.castLE h i))) = v (Fin.natAdd (n + k) i))
        ↔ (∀ i : Fin j, Fin.init v (Fin.castAdd j (Fin.natAdd n (Fin.castLE hj i)))
            = Fin.init v (Fin.natAdd (n + k) i))
          ∧ Fin.init v (Fin.castAdd j (Fin.natAdd n ⟨j, h⟩)) = v (Fin.last (n + k + j)) :=
      Fin.forall_fin_succ'
    by_cases hB : ∀ i : Fin j, Fin.init v (Fin.castAdd j (Fin.natAdd n (Fin.castLE hj i)))
        = Fin.init v (Fin.natAdd (n + k) i)
    · by_cases hA : Fin.init v (Fin.castAdd j (Fin.natAdd n ⟨j, h⟩)) = v (Fin.last (n + k + j))
      · rw [if_pos hA, if_pos hB, if_pos (hiff.mpr ⟨hB, hA⟩)]
        rfl
      · rw [if_neg hA, if_neg (fun hh => hA (hiff.mp hh).2)]
    · rw [if_neg hB, if_neg (fun hh => hB (hiff.mp hh).1)]
      split_ifs <;> rfl

/-- A diagonal letter's referee multiplies by its phase. -/
private theorem letterAmp_diagonal_diagonalInjection {N m : ℕ} (D : DiagPhase N m)
    (F : (Fin N → ZMod 2) → ℂ) (w : Fin N → ZMod 2) :
    letterAmp (GateLetter.diagonal D) F w = charOf m (D.eval w) * F w :=
  rfl

/-- **The protocol's referee** on the input's amplitude, read at the outcome string `c`: where the
ancillas equal `c`, `ζ^{f(x ∘ q)}` times the register's at `x`; zero elsewhere. -/
private theorem interpretAmp_diagonalInjectionProtocol {m k : ℕ} (q : Fin k → Fin n)
    (f : DiagPhase k m) (s : (Fin n → ZMod 2) → ℂ) (c : Fin k → ZMod 2)
    (u : Fin (n + k) → ZMod 2) :
    (diagonalInjectionProtocol q f).interpretAmp
        (fun u => charOf m (f.eval fun i => u (Fin.natAdd n i))
          * s (fun i => u (Fin.castAdd k i))) (Fin.append u c)
      = if (fun i => u (Fin.natAdd n i)) = c then
          charOf m (f.eval fun i => u (Fin.castAdd k (q i))) * s (fun i => u (Fin.castAdd k i))
        else 0 := by
  unfold diagonalInjectionProtocol
  rw [Protocol.interpretAmp_word, runAmp_cons, runAmp_nil, letterAmp_diagonal_diagonalInjection,
    interpretAmp_measureAncillas q f s k le_rfl, correctionPhase_eval]
  simp only [Fin.append_left, Fin.append_right, Fin.castLE_refl]
  by_cases hc : (fun i => u (Fin.natAdd n i)) = c
  · have hci : ∀ i, u (Fin.natAdd n i) = c i := fun i => congrFun hc i
    rw [if_pos hci, if_pos hc]
    unfold injectAmp
    have hx : (fun i => u (Fin.natAdd n i) + u (Fin.castAdd k (q i)))
        = fun i => u (Fin.castAdd k (q i)) + c i := by
      funext i
      rw [hci i, add_comm]
    rw [hx, ← mul_assoc, charOf_sub_mul]
  · have hci : ¬ ∀ i, u (Fin.natAdd n i) = c i := fun h => hc (funext h)
    rw [if_neg hci, if_neg hc, mul_zero]

/-! ## Weights -/

/-- **The input's weight** is `2^k` times the register's: each ancilla `∣0⟩ + ∣1⟩` doubles it, and
the magic state's phase has modulus one. -/
private theorem ampNormSq_input {m k : ℕ} (f : DiagPhase k m) {S : KernelSumState n}
    (hS : IsCarrier S) (hmk : S.m ≤ m) :
    ampNormSq (diagonalInjectionInput f S hmk)
      = 2 ^ k * ∑ x : Fin n → ZMod 2, Complex.normSq (amp S x) := by
  unfold ampNormSq
  rw [(diagonalInjectionInput_spec f hS hmk).2.2, ← sum_sum_append]
  simp only [Fin.append_left, Fin.append_right, Complex.normSq_mul,
    normSq_charOf, one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

/-! ## The scale along the processing -/

/-- The processed branch's scale is the register's times a power of `√2`, or zero. -/
private theorem scaledBy_diagonalInjectionBranch {m k : ℕ} (q : Fin k → Fin n)
    (f : DiagPhase k m) (S : KernelSumState n) (hmk : S.m ≤ m) (c : Fin k → ZMod 2) :
    ScaledBy S.c (diagonalInjectionBranch q f S hmk c).c := by
  have hI : ScaledBy S.c (diagonalInjectionInput f S hmk).c := by
    have h := scaledBy_run ([GateLetter.diagonal (MvPolynomial.rename (Fin.natAdd n) f)] :
      GateWord (n + k) m) (appendFreeBits k (liftPrecision S m hmk))
    rw [appendFreeBits_c] at h
    exact h
  exact ((hI.trans (scaledBy_interpret _ _)).trans (scaledBy_restrictLast k c _)).trans
    (scaledBy_restrictLast k c _)

/-! ## The processed branch -/

/-- **The gate's output, from the semantics**: `ζ^f` on the lifted register has amplitude
`ζ^{f(x ∘ q)}` times the register's at `x`; by `amp_run` and `amp_liftPrecision`. -/
theorem amp_run_diagonal_rename {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    {S : KernelSumState n} (hS : IsCarrier S) (hmk : S.m ≤ m) :
    amp (run ([GateLetter.diagonal (MvPolynomial.rename q f)] : GateWord n m)
        (liftPrecision S m hmk)) = fun x => charOf m (f.eval (x ∘ q)) * amp S x := by
  rw [amp_run ([GateLetter.diagonal (MvPolynomial.rename q f)] : GateWord n m)
    (isCarrier_liftPrecision hS m hmk) rfl, amp_liftPrecision]
  funext x
  simp only [runAmp_cons, runAmp_nil, letterAmp, DiagPhase.eval_rename]

/-- **The gate `ζ^f` on the register**, T05's run of `rename q f` on the lifted register: a carrier
state whose amplitude is `ζ^{f(x ∘ q)}` times the register's at `x`. -/
private theorem gate_spec {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    {S : KernelSumState n} (hS : IsCarrier S) (hmk : S.m ≤ m) :
    IsCarrier (run ([GateLetter.diagonal (MvPolynomial.rename q f)] : GateWord n m)
        (liftPrecision S m hmk)) ∧
      amp (run ([GateLetter.diagonal (MvPolynomial.rename q f)] : GateWord n m)
        (liftPrecision S m hmk)) = fun x => charOf m (f.eval fun i => x (q i)) * amp S x :=
  ⟨isCarrier_run _ (isCarrier_liftPrecision hS m hmk) rfl, amp_run_diagonal_rename q f hS hmk⟩

/-- **A processed branch, from its referee.** For any protocol on `n + k` free bits with `k`
outcome bits, run on a carrier input at its precision: if the referee on the input's amplitude,
read with the last `k` of the `n + k` bits and the outcome bits both at `c`, is a nonzero function
`G` of the first `n` bits, then the interpretation with the outcome bits dropped at `c`, and then
the last `k` bits dropped at `c`, is a carrier state of amplitude `G`. -/
theorem restrictLast_restrictLast_interpret_spec {m k : ℕ} (p : Protocol m (n + k) k)
    {I : KernelSumState (n + k)} (hI : IsCarrier I) (hIm : I.m = m) (c : Fin k → ZMod 2)
    {G : (Fin n → ZMod 2) → ℂ} (hG : G ≠ 0)
    (hp : ∀ x, p.interpretAmp (amp I) (Fin.append (Fin.append x c) c) = G x) :
    IsCarrier (restrictLast k c (restrictLast k c (p.interpret I))) ∧
      amp (restrictLast k c (restrictLast k c (p.interpret I))) = G := by
  obtain ⟨hPc, hPa⟩ := amp_interpret p hI hIm
  have hG₁ : (fun u => p.interpretAmp (amp I) (Fin.append u c)) ≠ 0 := by
    intro h0
    apply hG
    funext x
    rw [← hp x]
    exact congrFun h0 (Fin.append x c)
  obtain ⟨h₁c, h₁a⟩ := restrictLast_spec k c hPc hG₁ (fun u => by rw [hPa])
  exact restrictLast_spec k c h₁c hG (fun x => by rw [h₁a]; exact hp x)

/-- The protocol's interpretation read at the outcome string `c`: where the ancillas equal `c`, the
gate's amplitude at the register's bits; zero elsewhere. -/
private theorem amp_interpret_append {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    {S : KernelSumState n} (hS : IsCarrier S) (hmk : S.m ≤ m) (c : Fin k → ZMod 2)
    (u : Fin (n + k) → ZMod 2) :
    amp ((diagonalInjectionProtocol q f).interpret (diagonalInjectionInput f S hmk))
        (Fin.append u c)
      = if (fun i => u (Fin.natAdd n i)) = c then
          charOf m (f.eval fun i => u (Fin.castAdd k (q i))) * amp S (fun i => u (Fin.castAdd k i))
        else 0 := by
  obtain ⟨hIc, hIm, hIamp⟩ := diagonalInjectionInput_spec f hS hmk
  rw [(amp_interpret (diagonalInjectionProtocol q f) hIc hIm).2, hIamp]
  exact interpretAmp_diagonalInjectionProtocol q f (amp S) c u

/-- **The processed branch** is a carrier state with the gate's amplitude. -/
private theorem diagonalInjectionBranch_spec {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    {S : KernelSumState n} (hS : IsCarrier S) (hmk : S.m ≤ m) (c : Fin k → ZMod 2) :
    IsCarrier (diagonalInjectionBranch q f S hmk c) ∧
      amp (diagonalInjectionBranch q f S hmk c)
        = fun x => charOf m (f.eval fun i => x (q i)) * amp S x := by
  obtain ⟨hRc, hRamp⟩ := gate_spec q f hS hmk
  set G : (Fin n → ZMod 2) → ℂ := fun x => charOf m (f.eval fun i => x (q i)) * amp S x
    with hGdef
  have hG : G ≠ 0 := by
    rw [← hRamp]
    exact hRc.2.2.2
  set G₁ : (Fin (n + k) → ZMod 2) → ℂ := fun u =>
    if (fun i => u (Fin.natAdd n i)) = c then G (fun i => u (Fin.castAdd k i)) else 0 with hG₁def
  have hG₁ : ∀ x, G₁ (Fin.append x c) = G x := by
    intro x
    simp only [hG₁def, Fin.append_left, Fin.append_right, if_pos]
  have hG₁ne : G₁ ≠ 0 := fun h0 => hG (funext fun x => by rw [← hG₁ x, h0]; rfl)
  obtain ⟨hPc, -⟩ :=
    amp_interpret (diagonalInjectionProtocol q f) (diagonalInjectionInput_spec f hS hmk).1
      (diagonalInjectionInput_spec f hS hmk).2.1
  obtain ⟨h₁c, h₁amp⟩ := restrictLast_spec k c hPc hG₁ne (amp_interpret_append q f hS hmk c)
  exact restrictLast_spec k c h₁c hG (fun x => by rw [h₁amp]; exact hG₁ x)

/-- **The protocol's branch at `c` has the register's weight**: the branch is the gate's amplitude
where the ancillas equal `c`, and zero elsewhere. -/
private theorem branchWeight_diagonalInjection {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    {S : KernelSumState n} (hS : IsCarrier S) (hmk : S.m ≤ m) (c : Fin k → ZMod 2) :
    (diagonalInjectionProtocol q f).branchWeight (diagonalInjectionInput f S hmk) c
      = ∑ x : Fin n → ZMod 2, Complex.normSq (amp S x) := by
  unfold Protocol.branchWeight Protocol.branch
  refine (Finset.sum_congr rfl fun u _ =>
    congrArg Complex.normSq (amp_interpret_append q f hS hmk c u)).trans ?_
  rw [← sum_sum_append, Finset.sum_eq_single c]
  · simp only [Fin.append_left, Fin.append_right, if_pos, Complex.normSq_mul,
      normSq_charOf, one_mul]
  · intro o _ ho
    refine Finset.sum_eq_zero fun x _ => ?_
    simp only [Fin.append_right]
    rw [if_neg ho, map_zero]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-! ## The correction's degree -/

/-- The chosen data qubits, read off the register's and the ancillas' bits, as an additive map. -/
private def dataBits {k : ℕ} (q : Fin k → Fin n) : (Fin (n + k) → ZMod 2) →+ (Fin k → ZMod 2) where
  toFun w i := w (Fin.castAdd k (q i))
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The correction in the branch at `c`** is minus the difference of `f` in the direction `c`,
read at the chosen data qubits. -/
private theorem correction_eq_neg_fwdDiff {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    (c : Fin k → ZMod 2) :
    (fun w : Fin (n + k) → ZMod 2 => (correctionPhase q f).eval (Fin.append w c))
      = -(fwdDiff c f.eval ∘ dataBits q) := by
  funext w
  have h1 : (fun i => Fin.append w c (Fin.castAdd k (Fin.castAdd k (q i))))
      = fun i => w (Fin.castAdd k (q i)) :=
    funext fun i => Fin.append_left w c _
  have h2 : (fun i => Fin.append w c (Fin.castAdd k (Fin.castAdd k (q i)))
        + Fin.append w c (Fin.natAdd (n + k) i))
      = fun i => w (Fin.castAdd k (q i)) + c i :=
    funext fun i => by rw [Fin.append_left, Fin.append_right]
  rw [correctionPhase_eval, h1, h2]
  exact (neg_sub _ _).symm

/-- The first clause of `correction_degree_lt`: a degree bound `d + 1` on `f` gives `d` on the
correction. -/
private theorem correction_degree_le {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    (c : Fin k → ZMod 2) (d : ℕ) (hf : IsPolyDegLE (d + 1) f.eval) :
    IsPolyDegLE d fun w : Fin (n + k) → ZMod 2 => (correctionPhase q f).eval (Fin.append w c) := by
  rw [correction_eq_neg_fwdDiff]
  exact ((hf.fwdDiff c).comp_addMonoidHom_right (dataBits q)).neg

/-! ## The statements -/

-- source: papers/clifford_hierarchy/
-- Gottesman_Chuang_1999_universal_via_teleportation_quant-ph_9908010 figure:fig:ftqc-ck
-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:c3
/-- **The correction's nonclassical degree is one below `f`'s.** For every outcome string `c`, the
correction's exponent in the branch at `c`, as a function of the register's and the ancillas'
bits, `w ↦ f(w ∘ q) − f(w ∘ q ⊕ c)`, has degree at most `d` whenever `f` has degree at most
`d + 1` (`IsPolyDegLE`, ECCLib's nonclassical degree); and for a multilinear `f` it has degree at
most `effectiveLevel f − 1`, `f`'s level in the hierarchy less one. Proved at T22.3.2. -/
theorem correction_degree_lt {m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    (c : Fin k → ZMod 2) :
    (∀ d : ℕ, IsPolyDegLE (d + 1) f.eval →
        IsPolyDegLE d fun w : Fin (n + k) → ZMod 2 => (correctionPhase q f).eval (Fin.append w c))
      ∧ (DiagPhase.IsMultilinear f →
        IsPolyDegLE (DiagPhase.effectiveLevel f - 1)
          fun w : Fin (n + k) → ZMod 2 => (correctionPhase q f).eval (Fin.append w c)) := by
  refine ⟨correction_degree_le q f c, fun hP => ?_⟩
  have hF := FTQCLib.Bridge.eval_isPolyDegLE_effectiveLevel f hP
  exact correction_degree_le q f c _ (hF.mono (by omega))

-- source: papers/clifford_hierarchy/
-- Gottesman_Chuang_1999_universal_via_teleportation_quant-ph_9908010 paragraph:hbf3d766785fe
-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:basic2
/-- **The injection of any diagonal gate is correct.** For every carrier state `S`, at any height
and any precision `S.m ≤ m`, every phase polynomial `f` on `k` qubits at precision `m`, every map
`q` choosing the data qubits and every outcome string `c`, run on the register beside the magic
state `ζ^f ∣+⟩^{⊗k}`: the protocol's branch at `c` has weight `2^{−k}` of that input's (T14's
`branchWeight`, D3); the branch processed (the outcome bits evaluated at `c` and dropped, each
ancilla dropped at its outcome) has weight `2^{−k}` of the input's, is a carrier state, is
`StateEq` to `ζ^f` applied to the register, T05's run of the diagonal letter `rename q f` on the
register lifted to precision `m` (D8), and is related to it by T07's rules. The ancillas
`∣0⟩ + ∣1⟩` multiply the register's weight by `2^k`, so `2^{−k}` of the input's is the register's
own. Proved at T22.3.1. -/
theorem diagonalInjection_correct {m k : ℕ} {S : KernelSumState n} (hS : IsCarrier S)
    (hmk : S.m ≤ m) (q : Fin k → Fin n) (f : DiagPhase k m) (c : Fin k → ZMod 2) :
    (diagonalInjectionProtocol q f).branchWeight (diagonalInjectionInput f S hmk) c
        = ampNormSq (diagonalInjectionInput f S hmk) / 2 ^ k ∧
      ampNormSq (diagonalInjectionBranch q f S hmk c)
        = ampNormSq (diagonalInjectionInput f S hmk) / 2 ^ k ∧
      IsCarrier (diagonalInjectionBranch q f S hmk c) ∧
      StateEq (diagonalInjectionBranch q f S hmk c)
        (run ([GateLetter.diagonal (MvPolynomial.rename q f)] : GateWord n m)
          (liftPrecision S m hmk)) ∧
      Relation.EqvGen CarrierRule (diagonalInjectionBranch q f S hmk c)
        (run ([GateLetter.diagonal (MvPolynomial.rename q f)] : GateWord n m)
          (liftPrecision S m hmk)) := by
  obtain ⟨hBc, hBamp⟩ := diagonalInjectionBranch_spec q f hS hmk c
  obtain ⟨hRc, hRamp⟩ := gate_spec q f hS hmk
  have hW : ampNormSq (diagonalInjectionInput f S hmk) / 2 ^ k
      = ∑ x : Fin n → ZMod 2, Complex.normSq (amp S x) := by
    rw [ampNormSq_input f hS hmk]
    field_simp
  have hst : StateEq (diagonalInjectionBranch q f S hmk c)
      (run ([GateLetter.diagonal (MvPolynomial.rename q f)] : GateWord n m)
        (liftPrecision S m hmk)) :=
    hBamp.trans hRamp.symm
  refine ⟨by rw [hW]; exact branchWeight_diagonalInjection q f hS hmk c, ?_, hBc, hst, ?_⟩
  · rw [hW]
    unfold ampNormSq
    rw [hBamp]
    simp only [Complex.normSq_mul, normSq_charOf, one_mul]
  · exact eqvGen_carrierRule_of_scaledBy hBc hRc hst (scaledBy_diagonalInjectionBranch q f S hmk c)
      (scaledBy_run ([GateLetter.diagonal (MvPolynomial.rename q f)] : GateWord n m)
        (liftPrecision S m hmk))

end FTQCLib.Frame.Walkthrough

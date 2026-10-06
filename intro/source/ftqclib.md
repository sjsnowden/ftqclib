# ftqclib: A Mathematical Foundation for Fault-Tolerant Quantum Computing

## Introduction

Quantum computing has acquired its language through the problems it has solved. A circuit describes how a computation is performed. A stabilizer specifies constraints on a state. A syndrome records evidence of an error. A magic state supplies a resource for a gate that is difficult to perform directly. These names preserve useful distinctions, but the mathematical connections between them are often left for the reader to reconstruct. Moving from circuits to error correction, or from pure states to noise, can feel like entering a succession of different subjects.

The connections are substantial. Commutation of Pauli operators is described by a bilinear pairing on binary vectors. Phases attached to bit strings can be studied as polynomial functions. Hadamard gates perform a finite Fourier transform. In a surface code, the distinction between a harmless closed error string and a logical error is expressed by homology. Recognizing these structures gives a reader ways to use mathematics already understood, and gives a researcher tools developed for more general problems.

**ftqclib is an effort to make these connections explicit, precise, and reusable.** It is a Lean 4 library, built on Mathlib, that develops mathematical descriptions of quantum computation and proves relationships between them. Lean checks proofs against the definitions and assumptions of each statement. A verified connection allows a result established in one description to be used in another, with the conditions of that translation visible.

The development brings together stabilizer geometry, the Clifford hierarchy, a calculus of finite sums of phases, measurement protocols, channels, and quantum error correction. A companion library, ECCLib, develops Fourier analysis, finite-field mathematics, classical codes, and verified classical decoding algorithms. The common foundation is useful because the subjects meet: the signs governing Pauli commutation also enter the Fourier description of noise, and that description leads to identities constraining quantum codes.

The intended beneficiaries include both readers and builders. A reader should be able to understand why several descriptions of a quantum process agree. A builder should be able to define a new transformation, encoding, or algorithm and state exactly what its correctness requires. Existing proofs can then support that construction instead of being reconstructed each time in a different notation.

This becomes especially valuable when direct classical simulation is too expensive to serve as the principal check on a quantum computation. A general proof can establish that a construction preserves its specified meaning without computing every output of every instance. Experimental evidence remains necessary to determine how faithfully hardware realizes the model.

The wider purpose is to make dependable quantum computing easier to understand and contribute to. Clear exposition and reusable formal mathematics can lower the cost of entering the field and combining results. Broader participation may, in turn, help produce better codes, algorithms, and implementations. Useful quantum computation and its public benefit are the goals of this effort; a shared, inspectable mathematical foundation is one way to work toward them.

## One state, several descriptions

Consider two qubits initially in the state $|00\rangle$. Apply a Hadamard gate to the first and then a controlled-NOT with the first as control. The result is the Bell state

$$
|\Phi^+\rangle=\frac{|00\rangle+|11\rangle}{\sqrt{2}}
=\frac{1}{\sqrt{2}}\sum_{t\in\{0,1\}}|t,t\rangle.
$$

The first expression displays its nonzero amplitudes. The second describes the same state using a single binary variable: choose a value of $t$, place it in both positions, and sum the two alternatives with the stated scale. The circuit, the amplitude vector, and the finite sum already offer three descriptions of one construction.

:::figure bell-pair.svg
**Figure 1.** The preparation circuit and the support of its output. Only the bit strings 00 and 11 have nonzero amplitude; both amplitudes are positive and equal to $1/\sqrt{2}$. The highlighted cells show support, not a classical mixture. Original SVG diagram for this essay, following the calculation above.
:::

There is also a description by constraints. The Bell state is fixed by applying $X$ to both qubits, and by applying $Z$ to both. Write these operations as $XX$ and $ZZ$.

:::proposition Bell-state characterization
The simultaneous $+1$ eigenspace of $XX$ and $ZZ$ is the one-dimensional space spanned by $|\Phi^+\rangle$.
:::

:::proof
Write a general state as $a|00\rangle+b|01\rangle+c|10\rangle+d|11\rangle$. The operation $ZZ$ leaves the equal-bit terms unchanged and negates the unequal-bit terms. Being fixed by it therefore forces $b=c=0$. The operation $XX$ exchanges $|00\rangle$ and $|11\rangle$, so being fixed by it then forces $a=d$. The resulting vectors are exactly the scalar multiples of $|00\rangle+|11\rangle$.
:::

This proof gives the stabilizer description a precise meaning. Normalization leaves only an overall phase unspecified. Changing a stabilizer sign changes the state: the $+1$ eigenspace of $ZZ$ intersected with the $-1$ eigenspace of $XX$ is spanned by $(|00\rangle-|11\rangle)/\sqrt{2}$. The signs carry information.

The commutation calculation itself can be expressed in binary arithmetic. Label an $n$-qubit Pauli, up to scalar phase, by two bit strings $a,b$: the entries of $a$ indicate where an $X$ occurs, and those of $b$ where a $Z$ occurs. For two labels define

$$
\omega\bigl((a,b),(c,d)\bigr)=a\cdot d+b\cdot c\pmod{2}.
$$

The corresponding Paulis commute when this value is zero and anticommute when it is one. The pairing counts, modulo two, the sign changes produced by passing an $X$ through a $Z$. It is called a symplectic form. For the two Bell stabilizers, $a=(1,1)$ for $XX$ and $d=(1,1)$ for $ZZ$, so the two sign changes cancel.

:::figure pauli-signs.svg
**Figure 2.** Commutation becomes parity. Each local exchange of $X$ and $Z$ contributes one minus sign. The two exchanges in $XX$ versus $ZZ$ cancel; the single exchange in $XI$ versus $ZI$ does not. Original SVG diagram of the symplectic calculation above.
:::

The gain is conceptual as well as computational. The binary span of a family of commuting Pauli labels is a subspace on which this pairing vanishes. Clifford gates act by transformations preserving the pairing. Signs and scalar phases require additional structure, which ftqclib treats explicitly. The library develops the connections between these geometric objects and their actions on quantum states. [1](#ref-stabilizers)

The corresponding Lean definition is short enough to read directly:

```lean
def omega (p q : Pauli n) : ZMod 2 :=
  (∑ i, p.Z i * q.X i) + (∑ i, p.X i * q.Z i)
```

Here `ZMod 2` means arithmetic modulo two, `p.X` and `p.Z` are the two binary components, and `∑ i` sums over qubit positions. The notation differs from the displayed equation, but the operation is exactly the same. Throughout this essay, Lean blocks are excerpts from the named source modules, with their surrounding imports and namespace context omitted. They show the actual definitions and proofs; they are not standalone programs.

## A common mathematical foundation

The Bell example suggests a general method: choose a representation that exposes the structure of a problem, and prove how that representation relates to the others.

For diagonal gates, the useful object is a phase function on bit strings. A gate multiplies each basis amplitude by a phase; powers of two in the phase denominator provide a natural precision parameter. Flipping an input bit compares two values of the function, producing a finite difference. Repeated differences connect polynomial arithmetic to the recursive definition of the Clifford hierarchy. The library formalizes the qubit classification of diagonal hierarchy gates, including the effective levels of familiar gates such as $S$, $T$, and CCZ. Global-phase conventions are part of the statements. [2](#ref-hierarchy)

Hadamards introduce sums, so a representation intended to follow general circuits must accommodate interference. The carrier calculus describes amplitudes through finite sums of polynomial phases, together with support and scale data. Some bits label the visible output; auxiliary bits are summed over. This provides a setting in which gate actions, changes of representation, and equality can be studied together.

:::figure interference.svg
**Figure 3.** A summed bit records alternatives that can interfere. Starting at zero, two Hadamards give two positive path contributions to output zero and opposite contributions to output one. Each path has magnitude one half. The intermediate bit is summed over; reading it would change the process. Original SVG path diagram of this elementary circuit identity.
:::

Fourier analysis supplies another connection. A layer of Hadamards is a normalized transform built from signs determined by binary dot products. The same sign patterns occur in code duality and channel representations. ECCLib develops finite Fourier analysis, classical coding identities, and verified decoding algorithms independently of FTQCLib: it imports Mathlib, while FTQCLib uses both. [3](#ref-ecclib)

Topology enters through error correction. In a lattice code, taking the boundary of an error string gives its syndrome. Closed strings have zero boundary, but some are boundaries of collections of faces and others represent logical operations. A chain complex records these relationships; homology records the remaining distinction. ftqclib develops this description alongside stabilizer and CSS algebra.

:::figure chains.svg
**Figure 4.** Why the boundary of a boundary vanishes. Each corner of the square occurs in two boundary edges and hence cancels in binary arithmetic. In the code interpretation, this identity underlies the compatibility of the checks. Original SVG diagram illustrating the chain-complex description.
:::

The source makes the familiar distinction using the kernel and image of linear maps:

```lean
def cycles (i : ℕ) : Submodule (ZMod 2) (Fin (C.cells i) → ZMod 2) :=
  LinearMap.ker (C.dFrom i).mulVecLin

/-- The boundaries of degree `i`: the image of the boundary `∂_{i+1}` into degree `i`. -/
def boundaries (i : ℕ) : Submodule (ZMod 2) (Fin (C.cells i) → ZMod 2) :=
  LinearMap.range (C.d i).mulVecLin
```

`LinearMap.ker` selects chains with zero boundary; `LinearMap.range` selects those that arise as boundaries of higher-dimensional chains. The subscript-like argument `i` is the dimension. At degree one, homology takes cycles modulo boundaries: it identifies strings differing by a stabilizer while retaining the logical distinction. These definitions come from `CSS.BasedComplex`.

## Meaning, transformation, and proof

Before an algebraic expression can be transformed safely, its meaning must be specified. For a carrier expression, this meaning is an amplitude function. For a gate word it is an action on amplitude functions. Measurement adds outcomes; forgetting part of a system leads to a channel. These assignments are the semantics of the representations.

### A carrier record and the state it denotes

Write $\mathcal{C}$ for a carrier record on an $n$-qubit register, and $\psi_{\mathcal{C}}$ for its amplitude function. The calligraphic letter names a mathematical presentation; the subscripted wavefunction names what that presentation means. Lowercase $c$ remains the record's scalar coefficient. This notation is expository: the Lean type is `KernelSumState n`.

A record has six fields:

$$
\mathcal{C}=(m,h,Q,c,L,x_0).
$$

| Field | Mathematical role | What the reader should picture |
| :--- | :--- | :--- |
| $m$ | Phase precision: exponents are read modulo $2^m$. | Which roots of unity can occur. |
| $h$ | Number of summed, or bound, bits. | Alternatives whose amplitudes must be added. |
| $Q$ | A phase polynomial in $n+h$ binary inputs. | The phase attached to each visible-word/summed-word pair. |
| $c$ | A complex scalar coefficient. | The overall scale and phase, before the factor from $h$. |
| $L$ | A subspace of binary Pauli labels. | Geometric data determining which visible words are permitted. |
| $x_0$ | An $n$-bit offset. | A translation of that permitted region. |

Let $\pi_X(L)$ be the set of $X$-components of labels in $L$. Define the affine region $A_{\mathcal{C}}=x_0+\pi_X(L)$, and put $\zeta_m=\exp(2\pi i/2^m)$. The record denotes

$$
\psi_{\mathcal{C}}(w)=\mathbf{1}_{A_{\mathcal{C}}}(w)\,
\frac{c}{(\sqrt{2})^h}\sum_{y\in\{0,1\}^h}\zeta_m^{Q(w,y)}.
$$

The indicator is one inside $A_{\mathcal{C}}$ and zero outside it. The exponent is evaluated modulo $2^m$; choosing another integer representative gives the same root of unity. The visible word $w$ labels an output basis state. The bound word $y$ is summed over and is not an additional output register. When $h=0$, there is one empty word, so the sum has one term.

The corresponding state vector is

$$
\lvert\psi_{\mathcal{C}}\rangle=\sum_{w\in\{0,1\}^n}\psi_{\mathcal{C}}(w)\lvert w\rangle.
$$

For an admissible carrier, $m\geq1$, $L$ is Lagrangian—a maximal commuting subspace of the binary Pauli labels—and this amplitude function is not identically zero. Unit normalization is a further property. Also, $A_{\mathcal{C}}$ is a **support envelope**: interference can make an amplitude zero even inside it. The datum $L$ must not in general be read as the stabilizer group of the denoted state; the phase polynomial and the sum also affect that state.

:::figure carrier-evaluation.svg
**Figure 5.** How a carrier record is read. Fix one visible word, test its geometric support condition, then add the phases of its bound alternatives and apply the recorded scale and normalization. Repeating this calculation gives the amplitude function. The diagram follows `CarrierAmplitude.amp` and `HadamardPhase.ampCore`; it is an explanatory SVG, not a proposed efficient evaluation algorithm.
:::

The record definition in Lean has precisely these six fields:

```lean
structure KernelSumState (n : ℕ) where
  m  : ℕ
  h  : ℕ
  Q  : DiagPhase (n + h) m
  c  : ℂ
  L  : Submodule (ZMod 2) (Pauli n)
  x₀ : Fin n → ZMod 2
```

`DiagPhase (n + h) m` records the polynomial's variables and precision in its type. `Fin n → ZMod 2` is an $n$-bit word. The raw record type stores the data; the separate predicate `IsCarrier` imposes the admissibility conditions just described.

### Two records for the same Bell pair

Return to $\lvert\Phi^+\rangle$. One record enforces equal output bits geometrically. Another permits all four output words and makes the unequal ones cancel. In the table, spans are over the two-element field, and the Pauli names denote their phase-free labels.

| Field | Geometric presentation $\mathcal{C}_{\mathrm{g}}$ | Sum presentation $\mathcal{C}_{\mathrm{s}}$ |
| :--- | :--- | :--- |
| $m$ | $1$ | $1$ |
| $h$ | $0$ | $1$ |
| $Q$ | $0$ | $(w_1+w_2)y$ modulo two |
| $c$ | $1/\sqrt{2}$ | $1/2$ |
| $L$ | $\operatorname{span}\{XX,ZZ\}$ | $\operatorname{span}\{XI,IX\}$ |
| $x_0$ | $00$ | $00$ |
| Support envelope | $\{00,11\}$ | $\{00,01,10,11\}$ |

For the geometric presentation, there is no bound bit and the permitted words simply receive amplitude $1/\sqrt{2}$. For the sum presentation, $\zeta_1=-1$, and each bound alternative contributes a sign:

| Visible word | Phase for $y=0$ | Phase for $y=1$ | Sum | Amplitude after scaling |
| :--- | :--- | :--- | :--- | :--- |
| $00$ | $+1$ | $+1$ | $2$ | $1/\sqrt{2}$ |
| $01$ | $+1$ | $-1$ | $0$ | $0$ |
| $10$ | $+1$ | $-1$ | $0$ | $0$ |
| $11$ | $+1$ | $+1$ | $2$ | $1/\sqrt{2}$ |

The common multiplier in the last column is $c/(\sqrt{2})^h=1/(2\sqrt{2})$. Thus the records differ in geometry, polynomial, scale, and bound-bit count, but $\psi_{\mathcal{C}_{\mathrm{g}}}=\psi_{\mathcal{C}_{\mathrm{s}}}$. The extra bit in the second presentation encodes cancellation; it does not turn the Bell pair into a three-qubit state. This is a small, explicit example of the representational freedom that a rewrite calculus must understand.

### How gates act on a carrier

For a gate $U$, write $\mathcal{G}_U$ for its operation on records. The correctness obligation is

$$
\psi_{\mathcal{G}_U(\mathcal{C})}=U\psi_{\mathcal{C}}.
$$

This is different from a rewrite between two presentations of the same state: a gate generally changes the amplitude function, while a representational rewrite preserves it. The library's gate words use three kinds of letter—diagonal gates, CNOT, and Hadamard—and each exposes a different part of the record.

**A diagonal gate changes phases.** If $U_D\lvert w\rangle=\zeta_m^{D(w)}\lvert w\rangle$, add its polynomial to the visible part of the exponent:

$$
Q_{\mathrm{new}}(w,y)=Q(w,y)+D(w).
$$

The direct sum rule keeps $m,h,c,L,x_0$ unchanged. At precision one, applying $Z$ to the first Bell qubit adds $w_1$ and changes the sign of the $11$ amplitude. At precision three, $T$ adds $w_1$ and multiplies that amplitude by $\exp(i\pi/4)$. To express the same original phases at higher precision, the existing exponent must be rescaled: lifting from $m$ to $M$ replaces $Q$ by $2^{M-m}Q$. Merely changing the precision field would change the state.

**CNOT relabels visible words.** With control one and target two, let $P(w_1,w_2)=(w_1,w_2\mathbin{\oplus}w_1)$. Since $P$ is its own inverse, the output amplitude at $w$ is the old amplitude at $P(w)$. The record substitutes this bit map into $Q$, sends $x_0$ to $P(x_0)$, and transforms $L$ by the corresponding symplectic Pauli map. The bound-bit count and scalar stay the same. For the geometric Bell record, the permitted words $00,11$ become $00,10$, giving $\lvert+0\rangle$. Polynomial substitution must represent binary XOR at the record's precision; ordinary integer addition is not interchangeable with it.

**Hadamard mixes amplitudes.** Its action on bit $k$ is

$$
(H_k\psi)(w)=\frac{1}{\sqrt{2}}\sum_{b\in\{0,1\}}(-1)^{w_kb}\psi(w[k\leftarrow b]).
$$

Here $w[k\leftarrow b]$ means replace the $k$th bit by $b$. When the support envelope is closed under flipping that bit, the library's free rule can absorb this sum into the record: adjoin $b$ as a bound bit, replace the old visible coordinate by $b$ in $Q$, and add $2^{m-1}w_kb$ to the exponent. Increasing $h$ by one supplies the required factor $1/\sqrt{2}$. The general gate runner uses a different, support-changing rule when that flip-closure condition fails; Hadamard does not always add a bound bit.

For example, present $\lvert+\rangle$ by $m=1$, $h=0$, $Q=0$, $c=1/\sqrt{2}$, and full one-bit support. The free Hadamard rule gives $h=1$ and $Q(w,b)=wb$:

$$
\psi_{\mathcal{G}_H(\mathcal{C}_{+})}(w)=\frac{1}{2}\sum_{b\in\{0,1\}}(-1)^{wb}.
$$

At $w=0$ the two signs add, giving one; at $w=1$ they cancel, giving zero. The output is $\lvert0\rangle$. Its record still permits both visible words, even though only one has nonzero amplitude. A later rewrite may express the same output with no bound bit and support envelope $\{0\}$.

The summed bit labels the input basis components whose amplitudes interfere. It is neither an extra physical qubit nor a measurement record. The carrier retains an unevaluated sum; simplifying that sum changes the description without changing the state. Actually measuring the qubit in the computational basis before applying the Hadamard would change the experiment: the interference responsible for the certain zero output would disappear.

An **ideal computational-basis measurement** distinguishes the alternatives zero and one and produces a classical outcome. It does not merely reveal a bit value that the superposition already possessed. Mathematically, let $P_b$ retain the basis components in which the measured bit equals $b$, setting the others to zero. For a normalized input $\lvert\psi\rangle$, the Born rule gives

$$
p_b=\lVert P_b\lvert\psi\rangle\rVert^2.
$$

If outcome $b$ occurs and $p_b>0$, the conditional state is $P_b\lvert\psi\rangle/\sqrt{p_b}$. The projection selects a branch; its squared norm gives the probability; dividing by $\sqrt{p_b}$ normalizes the selected branch. This describes this particular ideal measurement. Other measurement bases distinguish other alternatives.

For $\lvert+\rangle$, the two outcomes each have probability one half, leaving $\lvert0\rangle$ or $\lvert1\rangle$ respectively. Applying $H$ afterwards therefore produces $\lvert+\rangle$ or $\lvert-\rangle$, where $\lvert-\rangle=(\lvert0\rangle-\lvert1\rangle)/\sqrt{2}$. A final computational-basis measurement gives zero and one with equal probability in either case. Without the intervening measurement, the same final test gives zero with certainty.

Keeping the classical outcome lets us describe the state conditional on it and choose a later correction. Forgetting the outcome means averaging the branches with their probabilities; it does not mean adding their amplitudes back into a superposition. Physically, an apparatus can become correlated with the measured alternatives. When its distinguishing record is treated as classical or left unread, the qubit alone no longer has the coherence needed for the original cancellation. By contrast, the bound bit in the carrier sum creates no such record: its alternatives remain terms in a coherent amplitude calculation. The later discussion of protocols and unread information makes this distinction explicit for larger registers.

:::figure carrier-gates.svg
**Figure 6.** The three gate actions at the level of a record: modify phase values, relabel visible words and their support, or mix alternatives through a Hadamard sum. The rightmost column gives the examples developed in the text. Original SVG schematic of the verified gate semantics; the Hadamard row depicts the free-rule case.
:::

The Lean definition of the action on amplitude functions mirrors this account:

```lean
noncomputable def letterAmp {m : ℕ} (g : GateLetter n m) (f : (Fin n → ZMod 2) → ℂ) :
    (Fin n → ZMod 2) → ℂ :=
  match g with
  | .hadamard k => walshTransform k f
  | .diagonal D => fun w => charOf m (D.eval w) * f w
  | .cnot i j _ => fun w => f (cnotBitMap i j w)
```

The source then proves that running the corresponding record operations has exactly this amplitude action and preserves `IsCarrier`, when the record and word have matching precision. Those results are `amp_run` and `isCarrier_run` in `Carrier.GateWord`. The formula, table, and diagram therefore describe both an intuitive calculation and the meaning against which the implementation is proved correct.


A calculus supplies rules for changing a representation. A rule is sound when it preserves the specified meaning. For example, eliminating a summed variable is sound only when the resulting expression accounts correctly for cancellation, normalization, and any remaining phase. A locally plausible manipulation can fail if one of those factors is omitted.

:::figure semantics.svg
**Figure 7.** A semantic correctness statement. A transformation changes the description of a process; its proof establishes that the two descriptions have the same specified action. The diagram expresses the obligation, not an automatic verification procedure. Original SVG diagram for this essay.
:::

Soundness answers whether the rules are safe. Completeness asks a converse question: when two descriptions have the same meaning, can the rules connect them? ftqclib gives an exact answer for its carrier rules, including a restriction on scale.

The recorded scale multiplies the whole finite sum. Different presentations can distribute factors differently between this scale and the sum, even when their amplitudes agree. Precision controls which roots of unity may appear as phases. The theorem concerns the library's specified class of admissible carrier presentations, defined by `IsCarrier`; these have positive precision, prescribed support geometry, and a nonzero amplitude function. They need not be normalized states.

:::theorem Carrier rewrite completeness
Let $S$ and $T$ be admissible carrier presentations as specified above. A finite chain of carrier rules, allowing either direction of a rule, connects $S$ and $T$ if and only if their amplitude functions are equal and the ratio of their recorded scales is dyadic. Here a dyadic ratio means a root of unity of power-of-two order multiplied by an integer power of $\sqrt{2}$.
:::

The equality is exact equality of amplitudes. The scale condition refers to the presentations themselves. Equal amplitudes alone do not guarantee that these particular rules connect two presentations. The source also proves conservativity: related carrier states at the same precision can be connected by a chain staying within carrier states at that precision. [4](#ref-completeness)

:::proof-sketch
Soundness gives one direction: each rule preserves amplitudes and changes the scale only by an allowed factor. For the other direction, the proof puts the presentations into forms that can be compared and reduces their comparison to algebraic relations among roots of unity. It then realizes those relations using the rewrite rules. The conservativity argument carries out the matching at the states' original precision. The source contains the detailed arithmetic and constructions needed for these steps.
:::

Completeness provides a foundation for equational reasoning. Finding a short derivation or a useful simplification strategy is a further algorithmic problem. A formal calculus gives such algorithms a precise target: a proposed transformation can be checked against a defined meaning and justified by established results.

Here is the theorem and its final proof from `Carrier.RewriteCompleteness`:

```lean
theorem rewrite_complete {S T : KernelSumState n} (hS : IsCarrier S) (hT : IsCarrier T) :
    Relation.EqvGen CarrierRule S T ↔ StateEq S T ∧ IsDyadicRatio (T.c / S.c) := by
  constructor
  · intro hST
    obtain ⟨hs, r, hr, hc⟩ := stateEq_scale_of_eqvGen hST
    refine ⟨hs, ?_⟩
    rw [hc, mul_div_assoc, div_self (c_ne_zero_of_isCarrier hS), mul_one]
    exact hr
  · rintro ⟨hs, hd⟩
    exact eqvGen_of_stateEq hS hT hs hd
```

The symbol `↔` divides the two directions of the equivalence, while `∧` joins amplitude equality to the scale condition. `Relation.EqvGen` permits finite chains of rules in either direction. After `by`, `constructor` starts the two directions of the proof. Each bullet supplies one. The short final proof rests on substantial earlier lemmas: its brevity shows how completed arguments can become reusable components, rather than how little mathematics was required.

## Measurement and information left unread

A fault-tolerant computation includes measurements and operations chosen from their outcomes. ftqclib represents a protocol as a sequence of gate words and conditioning steps. A conditioning step introduces an outcome bit. Later operations may depend on outcome bits already present, and evaluating the outcome bits selects a branch. The development proves agreement with amplitude semantics and conservation of the total branch weight. [5](#ref-protocol)

Keeping an outcome as a coherent register and treating it as a classical record are different operations. This distinction can be seen in the Bell example. Measuring both Bell qubits in the computational basis produces equal outcomes with probabilities one half each. The resulting distribution records those probabilities, but it does not retain the relative coherence of the original superposition.

Forgetting a subsystem can be expressed directly in terms of amplitudes. Write $f(x,u)$ for an amplitude, with $x$ denoting retained bits and $u$ unread bits. The retained system is described by

$$
\rho(x,y)=\sum_u f(x,u)\,f(y,u)^{\ast}.
$$

Here the star denotes complex conjugation. This Gram matrix sums over the unread alternatives. For a Bell pair with its second qubit unread, it gives equal diagonal entries and zero off-diagonal entries: the first qubit alone is maximally mixed. The off-diagonal contribution vanishes because the environmental states paired with its two values are orthogonal.

:::figure unread-bell.svg
**Figure 8.** What remains when the second Bell qubit is unread. The two alternatives are correlated with orthogonal unread states. Tracing over that qubit leaves equal populations and no off-diagonal coherence in the retained qubit. Original SVG diagram of the Gram-matrix calculation.
:::

The implementation follows the formula directly:

```lean
noncomputable def gram {k : ℕ} (f : (Fin (n + k) → ZMod 2) → ℂ) (x y : Fin n → ZMod 2) : ℂ :=
  ∑ u : Fin k → ZMod 2, f (Fin.append x u) * starRingEnd ℂ (f (Fin.append y u))
```

`Fin k → ZMod 2` is a string of $k$ bits; `Fin.append x u` joins retained and unread bits. `starRingEnd ℂ` takes complex conjugates. The word `noncomputable` permits a mathematical definition using the ambient complex-number infrastructure without promising an executable numerical procedure.

The distinction between exact amplitudes and unread information then becomes a theorem:

```lean
theorem unreadEq_of_stateEq {k : ℕ} {S T : KernelSumState (n + k)} (h : StateEq S T) :
    UnreadEq k S T := by
  intro x y
  unfold StateEq at h
  rw [h]
```

This proof from `Carrier.UnreadBits` introduces the two retained strings, unfolds the hypothesis of exact amplitude equality, and rewrites with it. Equal amplitudes therefore give equal Gram data. The converse would be stronger and is false in general: even an overall phase disappears from the Gram data. A small proof can make the direction of a translation quite explicit.

The library develops equality under this unread-bit interpretation, purification, and channels obtained from protocol dilations. Applying a protocol to one half of a Bell pair for each input qubit gives a Choi representation through which channel equality can be studied. It treats coherent and measured readings separately. For each read-outcome branch, it also relates descriptions of the channel in a Pauli basis. These offer different ways of recording its action, connected by a Fourier identity. [6](#ref-channels)

This extends the common foundation from pure-state computation to observable processes with discarded information. It also exposes boundaries of the gate language: the development proves arithmetic restrictions on channels realizable by its protocols. This snapshot does not prove the general converse needed to turn these restrictions into an exact synthesis theorem.

## Error correction as a mathematical construction

Two surface-code errors can produce the same syndrome. For either Pauli type, their difference is a cycle, relative to the relevant boundaries on a planar patch. A recovery succeeds when that difference acts trivially on the encoded information; a nontrivial logical string defeats it. The distinction between cycles and boundaries makes this familiar picture precise.

ftqclib constructs CSS codes from based chain complexes and identifies their logical spaces with homology and cohomology. It develops tensor products, relative complexes, and other constructions used to build codes. For its square-lattice toric and planar families, it proves the encoded-qubit counts and distance: two logical qubits on the torus, one on the planar patch, and distance $L$ at linear size $L$. The distance arguments include both lower bounds and explicit logical operators attaining them. [7](#ref-surface)

The encoding development starts from commuting signed Pauli generators whose phase-free binary labels are independent. It proves existence of a Clifford encoder and establishes how encoded states and logical Paulis behave, including the arrangement of multiple code blocks. The recovery theory proves a Knill–Laflamme equivalence: a specified family of errors is correctable exactly when its action on an encoded space satisfies the appropriate inner-product conditions. This expresses the requirement that information distinguishing errors must not reveal the protected logical state. [8](#ref-encoding)

The channel and Fourier mathematics meet coding theory again in quantum weight enumerators, MacWilliams identities, and bounds on code parameters. The development includes a Singleton bound for the stated stabilizer-code setting and a Hamming bound under nondegeneracy conditions. Those hypotheses are part of the results. [9](#ref-coding)

Such results can support new constructions without determining them in advance. A researcher might propose another chain complex, identify its logical operators, construct an encoder, and prove a distance bound using the existing infrastructure. A decoder requires its own algorithm and correctness argument. ECCLib already supplies verified classical decoders; using one in a quantum recovery procedure requires a proved connection to the quantum error model and code. The distinction helps locate the work still needed.

## Verification as computations grow

An arbitrary pure state of $n$ qubits has $2^n$ complex amplitudes. Directly storing and evolving all of them becomes expensive rapidly. Yet qubit count alone is not a test of classical difficulty: structure can make a large computation tractable, as stabilizer methods demonstrate. There is no universal transition at fifty qubits.

As useful computations enter regimes where direct simulation is infeasible, verification must draw on evidence other than exhaustive reproduction of their behavior. A theorem may quantify over every input to a transformation or over a whole family of codes. Checking that theorem does not require simulating every instance it covers. A proved circuit transformation can therefore remain applicable when calculating a particular circuit's output is difficult.

Formal proof has costs of its own. Definitions must express the intended problem, and difficult constructions can require difficult proofs. The advantage is that assumptions and dependencies become explicit, and checked results can be reused. Related projects pursue complementary parts of this task: VOQC verifies circuit optimizations, while Lean-QEC develops checked distance certificates for concrete code families. [10](#ref-related)

A mathematical guarantee also has a physical boundary. A proof establishes a relationship between a model and its specification. Calibration, device characterization, and experiments establish how faithfully hardware realizes that model. Fault-tolerant engineering needs these forms of evidence to work together. A proof about a specified noise model cannot by itself establish that a device has that noise.

For builders, a shared foundation creates concrete opportunities: check a transformation before applying it widely; establish an encoder's action on logical information; reuse code identities to constrain a proposed construction; or verify that a protocol's conditional corrections implement its intended process. Correctness then becomes something that can be carried through successive stages of development.

## From the surface code to a verified memory

The surface code provides a useful place to see how the work continues. Its geometry makes the abstract definitions visible, while using it as a memory requires the other parts of the library to meet: encoding, Pauli errors, measured syndromes, a decoder, and conditional correction.

:::figure surface-patch.svg
**Figure 9.** Two zero-syndrome possibilities on the library's unrotated $L=3$ planar patch, with thirteen data qubits on edges. The left loop bounds a face and acts as a stabilizer. The right three-edge string joins distinct rough boundaries and acts as a logical $Z$: its endpoints lie where the relevant checks are absent. Dashed lines are boundary guides, not additional data-qubit edges. The complementary $X$ picture uses the dual geometry and smooth boundaries. Original SVG diagram following the relative patch in `CSS.SurfaceCode`.
:::

One completed result says that the planar family has one logical qubit. Its final Lean proof reads:

```lean
theorem planarCode_k [NeZero L] :
    Module.finrank (ZMod 2) (cssZLogical (planarCode L).1 (planarCode L).2) = 1 := by
  -- `k = n - rk H_X - rk H_Z` with every star and every plaquette independent: the source's
  -- `L² + (L - 1)² - 2L(L - 1) = 1`.
  have hcss : IsCSSPair (planarCode L).1 (planarCode L).2 := cssOfComplex_isCSSPair _ _
  rw [finrank_cssZLogical hcss, rank_planarCode_fst, rank_planarCode_snd]
  have h := planarComplex_cells_one L
  omega
```

`[NeZero L]` requires a positive lattice size. `Module.finrank` is vector-space dimension, here over the two-element field. The proof rewrites the logical dimension in terms of the qubit count and check ranks, then uses the established lattice counts. Its final `omega` is Lean's arithmetic tactic; it is unrelated to the symplectic function named `omega` earlier. The distance theorem goes further: it gives lower bounds for both Pauli types and explicit logical strings attaining length $L$. [7](#ref-surface)

A distance theorem already contains the central idea of a recovery argument. For one Pauli type, let $e$ be an error and let $c$ be a minimum-weight correction with the same syndrome. Binary addition cancels edges occurring twice. Their sum has zero syndrome, and the minimum-weight property bounds its size.

:::proposition The distance argument for correction
Suppose a surface code has distance $L$ and its syndrome is measured without error. For either Pauli type, a minimum-weight correction recovers every error of weight at most $t$ whenever $2t<L$, up to a stabilizer and an overall phase.
:::

:::proof
The error itself is a candidate with the observed syndrome, so the chosen correction has weight at most that of the error. Their sum is a cycle (a relative cycle on the planar patch), and

$$
\operatorname{wt}(c+e)\leq\operatorname{wt}(c)+\operatorname{wt}(e)\leq 2t<L.
$$

By the distance bound, a cycle this small cannot represent a nontrivial logical operator. It is therefore a stabilizer boundary; for the complementary Pauli type, the same argument uses cocycles and coboundaries. Applying the correction preserves the encoded information. The two CSS error types can be treated separately.
:::

This is an explanatory proof of the geometric argument. Making it a theorem about an entire implemented protocol requires more: a proof that the ancilla circuit really extracts the specified syndrome, a proved connection between the decoder and the existing outcome-controlled Pauli word, and a proof that the corrected branches have the intended state and weight.

The inspected plan separates these stages. It marks the surface-code geometry and distance result **T34**, the encoding development **T29**, and Pauli errors and protocol locations **T64** as proved. It marks syndrome extraction **T30**, correction controlled by a decoder **T31**, and the integrated surface-code memory theorem **T65** as not done. These are statuses reported by the plan at the time of this revision. [11](#ref-plan)

:::figure surface-roadmap.svg
**Figure 10.** Selected steps from the inspected plan. The completed geometry and encoding results supply ingredients for the planned one-round memory theorem. Further work includes repeated noisy syndrome rounds, detector models, and lattice surgery. This is a guide to the programme, not the full dependency graph. Original SVG diagram based on targets T29–T31, T34, T53, T61, T64, and T65.
:::

The planned memory theorem assembles the stages into one statement: encode an input, apply a bounded-weight Pauli error, extract one ideal syndrome round, and apply a minimum-weight correction. Each nonzero branch should recover the encoded input up to a fourth root of unity determined by the error and correction. The decoder here is specified by its minimum-weight property; proving an efficient algorithm that realizes that specification is further work.

Beyond this one-round result, **T53** introduces repeated rounds, faults, and detector information in spacetime for the specified Clifford protocols. **T61** treats lattice surgery through the seam joining codes and the algebraic construction of the merged code, aiming to relate merge-and-split protocols to their logical action. These targets remain planned. The surgery target takes a logical-qubit-count hypothesis and does not by itself establish preservation of distance; noisy-round threshold guarantees also lie beyond the memory theorem. The plan places decoder implementation and hardware work in the companion `veriecc` programme.

This continuation shows what the common foundation is for. A proof about geometry becomes an ingredient in a recovery proof; a recovery proof becomes an ingredient in a statement about a measured, conditional computation. At each step, the new claim has a definite interface with the mathematics already established.

## Participation and the purpose of the project

The breadth of ftqclib serves an organizing purpose. A useful foundation for fault-tolerant quantum computing must let ideas cross the boundaries between algebra, geometry, algorithms, measurement, and noise. The current development provides substantial parts of that foundation, with further connections and applications still to be built.

Making those connections explicit can widen participation. A mathematician familiar with finite fields can approach quantum phases through polynomial arithmetic. A coding theorist can follow duality into stabilizer bounds. A computer scientist can approach circuit transformations through semantics. Accessible exposition gives these readers an entrance; formal definitions and proofs provide a place for their contributions to meet.

The aspiration is that a growing body of shared, verified mathematics will make exploration more dependable and its results easier to combine. Better codes and algorithms still require invention, and useful systems still require engineering. A foundation can reduce duplicated reasoning, expose assumptions, and allow later work to begin from guarantees already established. Helping more people contribute on those terms is a practical step toward quantum computation with broad public benefit.

## Sources and scope

This essay describes the source snapshot labelled **`d66ec2b`** in the [published ftqclib source browser](https://ftqclib.pages.dev/). The browser embeds 519 Lean modules; the relevant source files and theorem statements were inspected for this essay. The continuation also draws on the separately published plan, inspected on 5 October 2026. Its topic groupings are guides rather than an exhaustive account of the library. The essay is an exposition of that source, not a report of an independent Lean rebuild or a full audit of its proof dependencies. The Bell-state and minimum-weight-correction propositions are self-contained explanatory arguments. Lean excerpts reproduce source definitions or proofs, with surrounding file context omitted.

The references identify modules in the source browser. Select a module, then open its **Lean file** tab to read the embedded source. The module numbers in the links refer to this published snapshot; the browser does not automatically select a module from the URL fragment.

### 1. Stabilizers and their representations {#ref-stabilizers}

[FTQCLib source browser](https://ftqclib.pages.dev/): the `Pauli`, `Stabilizer`, and `Hilbert` developments, including the symplectic commutation form, signed stabilizers, and their operator interpretations. Foundational context: D. Gottesman, [*Stabilizer Codes and Quantum Error Correction*](https://arxiv.org/abs/quant-ph/9705052).

### 2. Diagonal gates and the hierarchy {#ref-hierarchy}

`FTQCLib.Hilbert.CGKCoverage` and the two-sided classification in `CGKTwoSided`, available through the [source browser](https://ftqclib.pages.dev/). Context: S. X. Cui, D. Gottesman, and A. Krishna, [*Diagonal gates in the Clifford hierarchy*](https://arxiv.org/abs/1608.06596). The repository's coverage is for qubits and records its phase conventions and corrections explicitly.

### 3. Fourier and classical coding mathematics {#ref-ecclib}

The `ECCLib` modules in the [source browser](https://ftqclib.pages.dev/), including finite and higher-order Fourier analysis, Gowers norms, Gauss sums, the Weil representation, code families, coding bounds, and decoding. `FTQCLib.Bridge.HOFBridge` connects finite differences and quantum phase polynomials.

### 4. The carrier calculus {#ref-completeness}

[`FTQCLib.Carrier.RewriteCompleteness`](https://ftqclib.pages.dev/#m-436): `rewrite_complete` and `rewrite_conservative`. [`PropCompleteness`](https://ftqclib.pages.dev/#m-471) gives the corresponding statement for presentations of morphisms. Prior mathematical context includes R. Vilmart, [*Completeness of Sum-Over-Paths for Toffoli-Hadamard and the Dyadic Fragments of Quantum Computation*](https://arxiv.org/abs/2205.02600).

The carrier definition and gate examples use [`HadamardPhase`](https://ftqclib.pages.dev/#m-295), [`CharSumGates`](https://ftqclib.pages.dev/#m-328), [`CarrierAmplitude`](https://ftqclib.pages.dev/#m-346), [`CarrierState`](https://ftqclib.pages.dev/#m-367), [`PrecisionGauge`](https://ftqclib.pages.dev/#m-380), and [`GateWord`](https://ftqclib.pages.dev/#m-427). The two Bell records are explanatory instances of these definitions. Calligraphic $\mathcal{C}$ names a record in this essay; it is not a new library type.

### 5. Measurement protocols {#ref-protocol}

[`FTQCLib.Carrier.Protocol`](https://ftqclib.pages.dev/#m-446): `amp_interpret`, `branch_weights_sum`, and the qualified `protocol_complete` theorem. The outcome register is part of the protocol interpretation.

### 6. Environments and channels {#ref-channels}

[`UnreadBits`](https://ftqclib.pages.dev/#m-473), [`Doubling`](https://ftqclib.pages.dev/#m-481), and [`PauliTransfer`](https://ftqclib.pages.dev/#m-490). In particular, `choi_eq_iff` concerns the coherent reading, `choi_measured_eq_iff` the measured reading, and `choi_mem_dyadic` a necessary arithmetic condition rather than a general synthesis converse. `PauliTransfer` connects Kraus operators' Pauli coefficients, the $\chi$ matrix, and the Pauli transfer matrix per read-outcome branch, including a Fourier relation between their diagonals.

### 7. Chain complexes and surface codes {#ref-surface}

[`FTQCLib.CSS.BasedComplex`](https://ftqclib.pages.dev/#m-275) and [`SurfaceCode`](https://ftqclib.pages.dev/#m-308): logical-space correspondences, `toricCode_k`, `planarCode_k`, `toricCode_distance`, and `planarCode_distance`, for the constructions and positive lattice sizes defined there.

### 8. Encoding and correctability {#ref-encoding}

[`FTQCLib.Codes.Encoding`](https://ftqclib.pages.dev/#m-493): `encoder_exists` and the encoded-state and logical-action results. [`Carrier.DoublingCorollaries`](https://ftqclib.pages.dev/#m-498): `knillLaflamme_iff` and `knillLaflamme_stabilizer_iff`. Context: E. Knill and R. Laflamme, [*A Theory of Quantum Error-Correcting Codes*](https://arxiv.org/abs/quant-ph/9604034).

### 9. Quantum coding identities and bounds {#ref-coding}

[`FTQCLib.Carrier.DoublingCorollaries`](https://ftqclib.pages.dev/#m-498): `quantum_macwilliams` and `pauli_twirl`. The bundled Singleton conclusion assumes at least one logical qubit; the Hamming conclusion requires the stated minimum-weight condition on nonzero normalizer elements.

### 10. Related verification work {#ref-related}

K. Hietala et al., [*A Verified Optimizer for Quantum Circuits*](https://arxiv.org/abs/1912.02250). M. Ehatamm et al., [*End-to-End Formalization of Quantum Error Correction*](https://arxiv.org/abs/2605.16523). These illustrate complementary uses of formal verification; no priority or performance comparison is asserted here.

### 11. Continuing work {#ref-plan}

[The ftqclib plan](https://ftqclib.pages.dev/plan/) (access-controlled), inspected on 5 October 2026. The page identifies its inputs as `docs/TARGETS.md` at `08f4171e1623` and `docs/STEPS.json` at `78711b2a934e`. The surface-code continuation uses targets T29–T31, T34, T53, T61, T64, and T65. Status labels describe this inspected version of the plan; planned statements are not presented as completed Lean theorems.

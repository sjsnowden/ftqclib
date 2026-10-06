/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.ControlledHadamard
import FTQCLib.Carrier.RewriteCompleteness

/-!
# The least height presenting controlled-H's output

T08 (`ControlledHadamard.lean`) runs the controlled-H word on any carrier state `S` and gets a
carrier state `W` whose amplitude is `controlledHAmp c t (amp S)`. The word decides `W`'s height,
and a stuck carrier state need not be of least height (T04), so `W.h` says nothing about how small
a carrier state presenting that function can be. This module states the least height over the
whole class of carrier states presenting the function (`docs/TARGETS.md`, T09), not over the
outputs of any one elimination strategy (decision 1 of `docs/decisions/T04.md`).

**The least height of a function** (`leastHeight`) is the infimum of the heights of the carrier
states whose amplitude is that function. Carrier states at every precision count. Two carrier
states presenting one function are `StateEq`, since `StateEq` is equality of amplitudes (D8), so
the class of carrier states presenting `amp W` is `W`'s whole `StateEq` class among carrier states.

**Rows of phases** (`HasRowSums f h r`): on an affine coset `x₀ + V` of `𝔽₂ⁿ` that holds the
support of `f`, each value `f w` is one common scale `r` times a sum of `2 ^ h` characters at one
precision `m`, one character for each bound word `y : Fin h → ZMod 2`, and each row chosen
independently of the others. This is the arithmetic the target names: the least height is read off
the row sums alone, with the exponent polynomial and the Lagrangian forgotten. Every function into
`ZMod (2 ^ m)` on a Boolean cube is the evaluation of an exponent (`exists_diagPhase_append`,
`BackwardConstructions.lean`), and every subspace `V` is the X-shadow of the Lagrangian
`{(x, z) | x ∈ V, z ∈ V^⊥}`; so a nonzero function with rows at height `h` is presented at height
`h` (proved here, the private `exists_isCarrier_of_hasRowSums`). At height zero every row is one
character and never vanishes, so the coset is then the support exactly; from height one on, a row
of antipodal pairs sums to zero and the coset may be all of `𝔽₂ⁿ`.

**The statement** (`leastHeight_controlledH`), for every carrier state `S` at any height and any
precision, distinct free bits `c ≠ t`, and the word run at any precision `k ≥ max S.m 3`, with
`f = controlledHAmp c t (amp S)` and `W` the word's output:

1. *The whole class.* A carrier state of height `h` in `W`'s `StateEq` class exists exactly when
   `leastHeight f ≤ h`. At `h = leastHeight f` this is attainment; for smaller `h` it is minimality;
   and the heights attained are all those above the least.
2. *Arithmetic.* `f` has rows of `2 ^ h` phases at some scale exactly when `leastHeight f ≤ h`: an
   exact characterisation of the least height for every input.
3. *The derivation class.* A carrier state of height `h` related to `W` by the equivalence
   `CarrierRule` generates (T07) exists exactly when `f` has rows of `2 ^ h` phases at a scale `r`
   whose ratio to the input's scale `S.c` is dyadic (D9). At `h = leastHeight f` this names the
   inputs where a carrier state of least height is related to the word's output by derivations,
   and the equivalence shows it fails on every other input.
4. *Dependence on the input.* The output's least height is within one of the input's:
   `leastHeight f ≤ leastHeight (amp S) + 1` and `leastHeight (amp S) ≤ leastHeight f + 1`.
   Controlled-H is its own inverse, so the two bounds are one argument used twice.

**Why item 3 is an equivalence and not attainment for every input.** The whole class and the
derivation class differ by the scale gap D9 names: `rewrite_complete` relates two carrier states
of one function only when their scales have a dyadic ratio, and a function may have a least-height
presentation only at a scale outside the input's dyadic class. An input of that kind (inferred by
hand computation, 2026-09-30; not proved here): at `n = 2`, `m = 1`, `h = 3`, scale `1`, the
exponent `y₀y₁y₂` on the bound bits and full support, so each row sums to `6` and the amplitude is
`3/√2` at every word. With control bit `0` and target bit `1`, controlled-H's output is `3/√2`,
`3/√2`, `3`, `0` at `00`, `01`, `10`, `11` (control first). Its support is three words, not a coset,
so its least height is at least one, and it is one: rows `1 + i`, `1 + i`, `2ζ₈`, `0` at the scale
`3/(√2(1 + i))`, whose modulus `3/2` is not a power of `√2`. At height one with a dyadic scale
`ζ·√2^e`, the row at `10` has modulus at most `2`, which forces `e ≥ 2`, and then the row at `00`
is `3/√2^(e+1)` times a root of unity, whose norm is not an integer, so it is not a sum of roots of
unity. So for this input no carrier state of least height is related to the word's output.

**What the target's prose says and this module does not.** `docs/TARGETS.md` (T09, "Exists") says
controlled-H's output needs precision at least three. That holds for some inputs and not for all:
where the control bit is `0` on the whole support the output is the input, at the input's own
precision (inferred). No precision appears in the statement: `HasRowSums` and `leastHeight` range
over every precision.

Everything here is frame-pure. No `FTQCLib.Hilbert` module is imported.

## Main definitions

* `leastHeight` — the least height of a carrier state presenting a function.
* `HasRowSums` — the function is a common scale times rows of `2 ^ h` characters on a coset
  holding its support.

## Main results

* `leastHeight_controlledH` — the four items above, for controlled-H's output on an arbitrary
  carrier state (T09; proved at T09.3).
* `hasRowSums_amp` — a carrier state has rows at its own height, the one step of the proof that
  `RowSumBounds.lean` needs too.

## Implementation notes

* `leastHeight f` is `sInf` of a set of natural numbers, so it is `0` when no carrier state presents
  `f`, as for the zero function. The statement is about `controlledHAmp c t (amp S)` and `amp S`,
  which T08 and `S` itself present, so the value there is never that default.
* Item 3 quantifies over carrier states `T` at every precision: `rewrite_complete` relates carrier
  states at any precisions.
* `W`'s scale is `S.c` divided by `√2` once for each H letter the representer rule `hRaise` runs;
  the free rule, the diagonal letters, the CNOT and the lift `liftPrecision` keep it (the private
  `exists_c_run`). So the ratio `W.c / S.c` is dyadic, and item 3 may name the input's scale in
  place of `W`'s.
* The proof (T09.3) reads the least height off rows. A carrier state has rows at its height
  (`hasRowSums_amp`), rows give a carrier state (`exists_isCarrier_of_hasRowSums`), and doubling
  each row raises the height by one (`HasRowSums.succ`); so rows exist exactly from the least
  height on. Controlled-H maps rows at height `h` to rows at height `h + 1`
  (`HasRowSums.controlledH`, at precision `m + 3`, where `√2` is the sum of the two eighth roots
  next to `1`), which with `controlledHAmp_involutive` gives item 4. Item 3 is `rewrite_complete`
  with the scale ledger. All of these but `hasRowSums_amp` are private.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The least height -/

/-- **The least height of a function**: the infimum of the heights of the carrier states, at any
precision, whose amplitude is `f`. It is `0` when no carrier state presents `f`. -/
noncomputable def leastHeight (f : (Fin n → ZMod 2) → ℂ) : ℕ :=
  sInf {h : ℕ | ∃ T : KernelSumState n, IsCarrier T ∧ amp T = f ∧ T.h = h}

/-! ## Rows of phases -/

/-- **Rows of `2 ^ h` phases at scale `r`.** On an affine coset `x₀ + V` holding the support of
`f`, each value `f w` is `r` times a sum of characters at one precision `m`, one character for each
bound word `y : Fin h → ZMod 2`, the characters of each row chosen independently of the other
rows. -/
def HasRowSums (f : (Fin n → ZMod 2) → ℂ) (h : ℕ) (r : ℂ) : Prop :=
  ∃ (m : ℕ) (x₀ : Fin n → ZMod 2) (V : Submodule (ZMod 2) (Fin n → ZMod 2)),
    (∀ w, f w ≠ 0 → w - x₀ ∈ V) ∧
      ∀ w, w - x₀ ∈ V →
        ∃ e : (Fin h → ZMod 2) → ZMod (2 ^ m), f w = r * ∑ y : Fin h → ZMod 2, charOf m (e y)

/-! ## Phase sums -/

/-- A sum of `2 ^ h` characters at precision `p`, one for each bound word. -/
private def IsPhaseSum (p h : ℕ) (z : ℂ) : Prop :=
  ∃ e : (Fin h → ZMod 2) → ZMod (2 ^ p), z = ∑ y : Fin h → ZMod 2, charOf p (e y)

/-- A residue at precision `m` read at precision `p ≥ m`: multiplied by `2 ^ (p - m)`. -/
private def liftValue (p : ℕ) {m : ℕ} (z : ZMod (2 ^ m)) : ZMod (2 ^ p) :=
  ((2 ^ (p - m) * z.val : ℕ) : ZMod (2 ^ p))

/-- The character of a lifted residue is the character of the residue. -/
private theorem charOf_liftValue {m p : ℕ} (hmp : m ≤ p) (z : ZMod (2 ^ m)) :
    charOf p (liftValue p z) = charOf m z := by
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  have hpow : 2 ^ (p - m) * 2 ^ m = 2 ^ p := by rw [← pow_add, Nat.sub_add_cancel hmp]
  have hlt : 2 ^ (p - m) * z.val < 2 ^ p :=
    hpow ▸ Nat.mul_lt_mul_of_pos_left (ZMod.val_lt z) (by positivity)
  unfold charOf liftValue
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  have hreal : (2 * Real.pi * ((2 ^ (p - m) * z.val : ℕ) : ℝ) / (2 : ℝ) ^ p)
      = 2 * Real.pi * (z.val : ℝ) / (2 : ℝ) ^ m := by
    have hpowR : (2 : ℝ) ^ (p - m) * (2 : ℝ) ^ m = (2 : ℝ) ^ p := by
      rw [← pow_add, Nat.sub_add_cancel hmp]
    rw [← hpowR]
    push_cast
    field_simp
  rw [hreal]

/-- The sum of the two primitive eighth roots of unity next to `1` is `√2`. -/
private theorem charOf_eighth_add {p : ℕ} (hp : 3 ≤ p) :
    charOf p (liftValue p (1 : ZMod (2 ^ 3))) + charOf p (liftValue p (-1 : ZMod (2 ^ 3)))
      = (Real.sqrt 2 : ℂ) := by
  rw [charOf_liftValue hp, charOf_liftValue hp, charOf_three_one, charOf_three_neg_one, ← add_div,
    div_eq_iff ofReal_sqrt_two_ne_zero, sqrt_two_mul_self]
  ring

/-- A phase sum times a character is a phase sum. -/
private theorem IsPhaseSum.mul_charOf {p h : ℕ} {z : ℂ} (hz : IsPhaseSum p h z)
    (a : ZMod (2 ^ p)) : IsPhaseSum p h (charOf p a * z) := by
  obtain ⟨e, rfl⟩ := hz
  refine ⟨fun y => e y + a, ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [charOf_add, mul_comm]

/-- The negation of a phase sum is a phase sum. -/
private theorem IsPhaseSum.neg {p h : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : IsPhaseSum p h z) :
    IsPhaseSum p h (-z) := by
  have h := hz.mul_charOf ((2 : ZMod (2 ^ p)) ^ (p - 1))
  rwa [charOf_two_pow_pred hp, neg_one_mul] at h

/-- A sign times a phase sum is a phase sum. -/
private theorem IsPhaseSum.signOf_mul {p h : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : IsPhaseSum p h z)
    (b : ZMod 2) : IsPhaseSum p h (signOf b * z) := by
  unfold signOf
  split
  · rwa [one_mul]
  · rw [neg_one_mul]
    exact hz.neg hp

/-- Two phase sums of `2 ^ h` terms make a phase sum of `2 ^ (h + 1)` terms. -/
private theorem IsPhaseSum.add {p h : ℕ} {z₁ z₂ : ℂ} (h₁ : IsPhaseSum p h z₁)
    (h₂ : IsPhaseSum p h z₂) : IsPhaseSum p (h + 1) (z₁ + z₂) := by
  classical
  obtain ⟨e₁, rfl⟩ := h₁
  obtain ⟨e₂, rfl⟩ := h₂
  refine ⟨fun y' => if y' (Fin.last h) = 0 then e₁ (Fin.init y') else e₂ (Fin.init y'), ?_⟩
  rw [sum_snoc_peel, sum_zmod_two]
  simp only [Fin.snoc_last, Fin.init_snoc, if_true, one_ne_zero, if_false]

/-- Zero is a phase sum of `2 ^ (h + 1)` terms: antipodal pairs. -/
private theorem isPhaseSum_zero {p : ℕ} (hp : 1 ≤ p) (h : ℕ) : IsPhaseSum p (h + 1) 0 := by
  have h₀ : IsPhaseSum p h (∑ _y : Fin h → ZMod 2, charOf p 0) := ⟨fun _ => 0, rfl⟩
  have h₁ := h₀.add (h₀.neg hp)
  rwa [add_neg_cancel] at h₁

/-- `√2` times a phase sum is a phase sum of twice as many terms, at precision at least three. -/
private theorem IsPhaseSum.sqrt_two_mul {p h : ℕ} (hp : 3 ≤ p) {z : ℂ}
    (hz : IsPhaseSum p h z) : IsPhaseSum p (h + 1) ((Real.sqrt 2 : ℂ) * z) := by
  have h₁ := (hz.mul_charOf (liftValue p (1 : ZMod (2 ^ 3)))).add
    (hz.mul_charOf (liftValue p (-1 : ZMod (2 ^ 3))))
  rwa [← add_mul, charOf_eighth_add hp] at h₁

/-- A phase sum at precision `m` is a phase sum at every precision `p ≥ m`. -/
private theorem IsPhaseSum.lift {m p h : ℕ} (hmp : m ≤ p) {z : ℂ} (hz : IsPhaseSum m h z) :
    IsPhaseSum p h z := by
  obtain ⟨e, rfl⟩ := hz
  exact ⟨fun y => liftValue p (e y),
    Finset.sum_congr rfl fun y _ => (charOf_liftValue hmp _).symm⟩

/-! ## Rows as phase sums -/

/-- `HasRowSums` with each row a phase sum. -/
private theorem hasRowSums_iff {f : (Fin n → ZMod 2) → ℂ} {h : ℕ} {r : ℂ} :
    HasRowSums f h r ↔
      ∃ (p : ℕ) (x₀ : Fin n → ZMod 2) (V : Submodule (ZMod 2) (Fin n → ZMod 2)),
        (∀ w, f w ≠ 0 → w - x₀ ∈ V) ∧
          ∀ w, w - x₀ ∈ V → ∃ z, IsPhaseSum p h z ∧ f w = r * z := by
  constructor
  · rintro ⟨p, x₀, V, hsupp, hrows⟩
    refine ⟨p, x₀, V, hsupp, fun w hw => ?_⟩
    obtain ⟨e, he⟩ := hrows w hw
    exact ⟨_, ⟨e, rfl⟩, he⟩
  · rintro ⟨p, x₀, V, hsupp, hrows⟩
    refine ⟨p, x₀, V, hsupp, fun w hw => ?_⟩
    obtain ⟨z, ⟨e, rfl⟩, he⟩ := hrows w hw
    exact ⟨e, he⟩

/-- Rows at height `h` give rows at height `h + 1`, each row doubled, at half the scale. -/
private theorem HasRowSums.succ {f : (Fin n → ZMod 2) → ℂ} {h : ℕ} {r : ℂ}
    (hrow : HasRowSums f h r) : HasRowSums f (h + 1) (r / 2) := by
  obtain ⟨p, x₀, V, hsupp, hrows⟩ := hasRowSums_iff.mp hrow
  refine hasRowSums_iff.mpr ⟨p, x₀, V, hsupp, fun w hw => ?_⟩
  obtain ⟨z, hz, hfz⟩ := hrows w hw
  refine ⟨z + z, hz.add hz, ?_⟩
  rw [hfz]
  ring

/-- Rows at height `h` give rows at every height `h + d`, at the scale divided by `2 ^ d`. -/
private theorem HasRowSums.add {f : (Fin n → ZMod 2) → ℂ} {h : ℕ} {r : ℂ}
    (hrow : HasRowSums f h r) (d : ℕ) : HasRowSums f (h + d) (r / 2 ^ d) := by
  induction d with
  | zero => simpa using hrow
  | succ d ih =>
    rw [← add_assoc, pow_succ, ← div_div]
    exact ih.succ

/-! ## The Lagrangian of a subspace -/

/-- The Lagrangian `{(x, z) | x ∈ V, z ⊥ V}`, whose X-shadow is `V`. -/
private def lagOf (V : Submodule (ZMod 2) (Fin n → ZMod 2)) : Submodule (ZMod 2) (Pauli n) where
  carrier := {q | q.X ∈ V ∧ ∀ v ∈ V, ∑ i, q.Z i * v i = 0}
  add_mem' := by
    rintro q q' ⟨hqX, hqZ⟩ ⟨hqX', hqZ'⟩
    refine ⟨by simpa using V.add_mem hqX hqX', fun v hv => ?_⟩
    simp [add_mul, Finset.sum_add_distrib, hqZ v hv, hqZ' v hv]
  zero_mem' := ⟨by simp, fun v _ => by simp⟩
  smul_mem' := by
    rintro a q ⟨hqX, hqZ⟩
    refine ⟨by simpa using V.smul_mem a hqX, fun v hv => ?_⟩
    simp [mul_assoc, ← Finset.mul_sum, hqZ v hv]

/-- The X-shadow of `lagOf V` is `V`. -/
private theorem map_xProj_lagOf (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule.map xProj (lagOf V) = V := by
  ext v
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq.1
  · intro hv
    exact ⟨⟨v, 0⟩, ⟨hv, fun _ _ => by simp⟩, rfl⟩

/-- `lagOf V` is isotropic. -/
private theorem isStabilizer_lagOf (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    IsStabilizer (lagOf V) := by
  intro q hq q' hq'
  unfold omega
  rw [hq.2 _ hq'.1]
  have h := hq'.2 _ hq.1
  rw [zero_add, ← h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A Pauli orthogonal to every pure-X Pauli `(v, 0)`, `v ∈ V`, has its Z-part orthogonal to
`V`. -/
private theorem sum_Z_mul_eq_zero {V : Submodule (ZMod 2) (Fin n → ZMod 2)} {a : Pauli n}
    (ha : ∀ v ∈ V, omega (⟨v, 0⟩ : Pauli n) a = 0) : ∀ v ∈ V, ∑ i, a.Z i * v i = 0 := by
  intro v hv
  have h := ha v hv
  unfold omega at h
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `lagOf V` is co-isotropic. -/
private theorem orthogonal_lagOf_le (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    LinearMap.BilinForm.orthogonal omegaBilin (lagOf V) ≤ lagOf V := by
  intro q hq
  have hq' : ∀ a ∈ lagOf V, omega a q = 0 := fun a ha =>
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hq) a ha
  refine ⟨?_, sum_Z_mul_eq_zero fun v hv => hq' ⟨v, 0⟩ ⟨hv, fun _ _ => by simp⟩⟩
  let A : Submodule (ZMod 2) (Pauli n) := Submodule.comap xProj V ⊓ LinearMap.ker zProj
  have hA : (⟨q.X, 0⟩ : Pauli n) ∈ A := by
    rw [← orthogonal_orthogonal_omegaBilin A]
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun a ha => ?_
    have haA : ∀ b ∈ A, omega b a = 0 := fun b hb =>
      (LinearMap.BilinForm.mem_orthogonal_iff.mp ha) b hb
    have haZ := sum_Z_mul_eq_zero (V := V) fun v hv => haA ⟨v, 0⟩ ⟨hv, by simp [zProj]⟩
    have h := hq' ⟨0, a.Z⟩ ⟨V.zero_mem, haZ⟩
    change omega a ⟨q.X, 0⟩ = 0
    unfold omega at h ⊢
    simpa using h
  exact hA.1

/-! ## Rows and carrier states -/

/-- **A carrier state's rows.** A carrier state has rows of `2 ^ h` phases at its own height, at
its scale divided by `√2 ^ h`. Public: `RowSumBounds.lean` reads the least height from below with
it. -/
theorem hasRowSums_amp (T : KernelSumState n) :
    HasRowSums (amp T) T.h (T.c / (Real.sqrt 2 : ℂ) ^ T.h) := by
  refine ⟨T.m, T.x₀, Submodule.map xProj T.L, fun w hw => ?_, fun w hw => ?_⟩
  · by_contra hn
    exact hw (amp_neg fun hs => hn ((mem_support_iff T w).mp hs))
  · refine ⟨fun y => T.Q.eval (Fin.append w y), ?_⟩
    rw [amp_pos ((mem_support_iff T w).mpr hw)]
    rfl

/-- **Rows give a carrier state.** A nonzero function with rows of `2 ^ h` phases at scale `r` is
the amplitude of a carrier state of height `h` and scale `r · √2 ^ h`. -/
private theorem exists_isCarrier_of_hasRowSums {f : (Fin n → ZMod 2) → ℂ} (hf : f ≠ 0) {h : ℕ}
    {r : ℂ} (hrow : HasRowSums f h r) :
    ∃ T : KernelSumState n, IsCarrier T ∧ amp T = f ∧ T.h = h
      ∧ T.c = r * (Real.sqrt 2 : ℂ) ^ h := by
  classical
  obtain ⟨m, x₀, V, hsupp, hrows⟩ := hrow
  let E : (Fin n → ZMod 2) → (Fin h → ZMod 2) → ZMod (2 ^ (m + 1)) := fun w =>
    if hw : w - x₀ ∈ V then fun y => liftValue (m + 1) (Classical.choose (hrows w hw) y) else 0
  obtain ⟨Q, hQ⟩ := exists_diagPhase_append (n := n) (m := m + 1) (h := h) E
  let T : KernelSumState n := ⟨m + 1, h, Q, r * (Real.sqrt 2 : ℂ) ^ h, lagOf V, x₀⟩
  have hsuppT : ∀ w, (∃ q ∈ T.L, w = T.x₀ + q.X) ↔ w - x₀ ∈ V := fun w => by
    rw [mem_support_iff T w]
    exact iff_of_eq (congrArg (w - x₀ ∈ ·) (map_xProj_lagOf V))
  have hamp : amp T = f := by
    funext w
    by_cases hw : w - x₀ ∈ V
    · rw [amp_pos ((hsuppT w).mpr hw), Classical.choose_spec (hrows w hw)]
      unfold ampCore
      rw [mul_div_cancel_right₀ _ (pow_ne_zero _ ofReal_sqrt_two_ne_zero)]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [exp_realPhase_eq_charOf, hQ]
      simp only [E, dif_pos hw]
      exact charOf_liftValue (Nat.le_succ m) _
    · rw [amp_neg fun hs => hw ((hsuppT w).mp hs)]
      by_contra hne
      exact hw (hsupp w (Ne.symm hne))
  refine ⟨T, ⟨Nat.le_add_left 1 m, isStabilizer_lagOf V, orthogonal_lagOf_le V, ?_⟩, hamp, rfl,
    rfl⟩
  rw [hamp]
  exact hf

/-! ## Controlled-H on rows -/

/-- Setting one bit moves a word along that bit's unit vector. -/
private theorem update_sub (w x₀ : Fin n → ZMod 2) (t : Fin n) (b : ZMod 2) :
    Function.update w t b - x₀ = (w - x₀) + (b - w t) • (Pi.single t 1 : Fin n → ZMod 2) := by
  funext j
  by_cases hj : j = t
  · subst hj
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Function.update_self,
      Pi.single_eq_same, smul_eq_mul, mul_one]
    ring
  · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Function.update_of_ne hj,
      Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero, add_zero]

/-- The two settings of one bit differ by that bit's unit vector. -/
private theorem update_one_sub_update_zero (w : Fin n → ZMod 2) (t : Fin n) :
    Function.update w t 1 - Function.update w t 0 = (Pi.single t 1 : Fin n → ZMod 2) := by
  funext j
  by_cases hj : j = t
  · subst hj
    simp
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

/-- Controlled-H where the control bit is `0`. -/
private theorem controlledHAmp_of_eq {c t : Fin n} {g : (Fin n → ZMod 2) → ℂ}
    {w : Fin n → ZMod 2} (hc : w c = 0) : controlledHAmp c t g w = g w :=
  if_pos hc

/-- Controlled-H where the control bit is `1`. -/
private theorem controlledHAmp_of_ne {c t : Fin n} {g : (Fin n → ZMod 2) → ℂ}
    {w : Fin n → ZMod 2} (hc : w c ≠ 0) :
    controlledHAmp c t g w = 1 / (Real.sqrt 2 : ℂ) *
      (g (Function.update w t 0) + signOf (w t) * g (Function.update w t 1)) :=
  if_neg hc

/-- **Controlled-H is its own inverse** on amplitude functions. -/
private theorem controlledHAmp_involutive {c t : Fin n} (hct : c ≠ t)
    (g : (Fin n → ZMod 2) → ℂ) : controlledHAmp c t (controlledHAmp c t g) = g := by
  funext w
  by_cases hc : w c = 0
  · rw [controlledHAmp_of_eq hc, controlledHAmp_of_eq hc]
  · have hb : ∀ b : ZMod 2, (Function.update w t b) c ≠ 0 := fun b => by
      rwa [Function.update_of_ne hct]
    rw [controlledHAmp_of_ne hc, controlledHAmp_of_ne (hb 0), controlledHAmp_of_ne (hb 1)]
    have h := congrFun (walshTransform_involutive t g) w
    simp only [walshTransform] at h
    rw [← h]

/-- The support of controlled-H's output lies over the support of its input: a nonzero output
value reads a nonzero input value at the word or at one of its two settings of the target. -/
private theorem controlledHAmp_ne_zero {c t : Fin n} {g : (Fin n → ZMod 2) → ℂ}
    {w : Fin n → ZMod 2} (hw : controlledHAmp c t g w ≠ 0) :
    g w ≠ 0 ∨ ∃ b : ZMod 2, g (Function.update w t b) ≠ 0 := by
  by_cases hc : w c = 0
  · rw [controlledHAmp_of_eq hc] at hw
    exact Or.inl hw
  · refine Or.inr ?_
    by_contra hno
    simp only [not_exists, not_not] at hno
    rw [controlledHAmp_of_ne hc, hno 0, hno 1] at hw
    exact hw (by ring)

/-- **Controlled-H on rows.** If `g` has rows of `2 ^ h` phases, controlled-H's output on `g` has
rows of `2 ^ (h + 1)` phases. Where the target's unit vector lies in the coset's direction `V`, the
scale is divided by `√2`: a row under control `0` is split by the two eighth roots next to `1`,
and a row under control `1` is the two input rows side by side. Otherwise the coset grows by the
target's unit vector and the scale is halved: a row under control `0` is doubled, a row under
control `1` reads one input row and splits it, and a row reading none is antipodal pairs. -/
private theorem HasRowSums.controlledH {g : (Fin n → ZMod 2) → ℂ} {h : ℕ} {r : ℂ}
    (hrow : HasRowSums g h r) (c t : Fin n) :
    ∃ r' : ℂ, HasRowSums (controlledHAmp c t g) (h + 1) r' := by
  classical
  obtain ⟨m, x₀, V, hsupp, hrows⟩ := hasRowSums_iff.mp hrow
  have hp3 : 3 ≤ m + 3 := Nat.le_add_left 3 m
  have hp1 : 1 ≤ m + 3 := by omega
  have hon : ∀ u, u - x₀ ∈ V → ∃ z, IsPhaseSum (m + 3) h z ∧ g u = r * z := fun u hu => by
    obtain ⟨z, hz, hgz⟩ := hrows u hu
    exact ⟨z, hz.lift (Nat.le_add_right m 3), hgz⟩
  have hoff : ∀ u, u - x₀ ∉ V → g u = 0 := fun u hu => by
    by_contra hne
    exact hu (hsupp u hne)
  by_cases hA : (Pi.single t 1 : Fin n → ZMod 2) ∈ V
  · have hu : ∀ w, w - x₀ ∈ V → ∀ b, Function.update w t b - x₀ ∈ V := fun w hw b => by
      rw [update_sub]
      exact V.add_mem hw (V.smul_mem _ hA)
    refine ⟨r / (Real.sqrt 2 : ℂ), hasRowSums_iff.mpr ⟨m + 3, x₀, V, fun w hw => ?_,
      fun w hw => ?_⟩⟩
    · rcases controlledHAmp_ne_zero hw with h0 | ⟨b, hb⟩
      · exact hsupp w h0
      · have h' := V.sub_mem (hsupp _ hb) (V.smul_mem (b - w t) hA)
        rwa [update_sub, add_sub_cancel_right] at h'
    · by_cases hc : w c = 0
      · obtain ⟨z, hz, hgz⟩ := hon w hw
        refine ⟨_, hz.sqrt_two_mul hp3, ?_⟩
        rw [controlledHAmp_of_eq hc, hgz, div_eq_mul_one_div r, one_div_sqrt_two]
        linear_combination (-(r * z) / 2) * sqrt_two_mul_self
      · obtain ⟨z₀, hz₀, hg₀⟩ := hon _ (hu w hw 0)
        obtain ⟨z₁, hz₁, hg₁⟩ := hon _ (hu w hw 1)
        refine ⟨_, hz₀.add (hz₁.signOf_mul hp1 (w t)), ?_⟩
        rw [controlledHAmp_of_ne hc, hg₀, hg₁, div_eq_mul_one_div r]
        ring
  · refine ⟨r / 2, hasRowSums_iff.mpr ⟨m + 3, x₀,
      V ⊔ Submodule.span (ZMod 2) {(Pi.single t 1 : Fin n → ZMod 2)}, fun w hw => ?_,
      fun w hw => ?_⟩⟩
    · rcases controlledHAmp_ne_zero hw with h0 | ⟨b, hb⟩
      · exact Submodule.mem_sup_left (hsupp w h0)
      · have hw' : w - x₀ = (Function.update w t b - x₀)
            + (w t - b) • (Pi.single t 1 : Fin n → ZMod 2) := by
          rw [update_sub, add_assoc, ← add_smul, sub_add_sub_cancel, sub_self, zero_smul,
            add_zero]
        rw [hw']
        exact Submodule.add_mem _ (Submodule.mem_sup_left (hsupp _ hb))
          (Submodule.mem_sup_right (Submodule.smul_mem _ _
            (Submodule.mem_span_singleton_self _)))
    · by_cases hc : w c = 0
      · by_cases hwV : w - x₀ ∈ V
        · obtain ⟨z, hz, hgz⟩ := hon w hwV
          refine ⟨z + z, hz.add hz, ?_⟩
          rw [controlledHAmp_of_eq hc, hgz]
          ring
        · refine ⟨0, isPhaseSum_zero hp1 h, ?_⟩
          rw [controlledHAmp_of_eq hc, hoff w hwV, mul_zero]
      · rw [controlledHAmp_of_ne hc, one_div_sqrt_two]
        by_cases h0 : Function.update w t 0 - x₀ ∈ V
        · by_cases h1 : Function.update w t 1 - x₀ ∈ V
          · exfalso
            have h' := V.sub_mem h1 h0
            rw [sub_sub_sub_cancel_right, update_one_sub_update_zero] at h'
            exact hA h'
          · obtain ⟨z₀, hz₀, hg₀⟩ := hon _ h0
            refine ⟨_, hz₀.sqrt_two_mul hp3, ?_⟩
            rw [hg₀, hoff _ h1]
            ring
        · by_cases h1 : Function.update w t 1 - x₀ ∈ V
          · obtain ⟨z₁, hz₁, hg₁⟩ := hon _ h1
            refine ⟨_, (hz₁.signOf_mul hp1 (w t)).sqrt_two_mul hp3, ?_⟩
            rw [hoff _ h0, hg₁]
            ring
          · refine ⟨0, isPhaseSum_zero hp1 h, ?_⟩
            rw [hoff _ h0, hoff _ h1]
            ring

/-! ## The scale along a word -/

/-- A letter divides the scale by a power of `√2`: `hRaise` by `√2`, every other rule by `1`. -/
private theorem exists_c_applyLetter {m : ℕ} (g : GateLetter n m) (S : KernelSumState n) :
    ∃ e : ℕ, (applyLetter g S).c = S.c / (Real.sqrt 2 : ℂ) ^ e := by
  cases g with
  | hadamard k =>
    rw [applyLetter_hadamard]
    unfold applyH
    split
    · exact ⟨1, by rw [pow_one]; rfl⟩
    · exact ⟨0, by rw [pow_zero, div_one]; rfl⟩
  | diagonal D =>
    refine ⟨0, ?_⟩
    rw [pow_zero, div_one]
    change (if hm : S.m = m then applyDiagSum S (hm ▸ D) else S).c = S.c
    split <;> rfl
  | cnot i j hij => exact ⟨0, by rw [pow_zero, div_one]; rfl⟩

/-- **The scale ledger of a word.** A run divides the scale by a power of `√2`. -/
private theorem exists_c_run {m : ℕ} (gs : GateWord n m) (S : KernelSumState n) :
    ∃ e : ℕ, (run gs S).c = S.c / (Real.sqrt 2 : ℂ) ^ e := by
  induction gs generalizing S with
  | nil => exact ⟨0, by rw [run_nil, pow_zero, div_one]⟩
  | cons g gs ih =>
    obtain ⟨e₁, he₁⟩ := exists_c_applyLetter g S
    obtain ⟨e₂, he₂⟩ := ih (applyLetter g S)
    exact ⟨e₁ + e₂, by rw [run_cons, he₂, he₁, div_div, pow_add]⟩

/-! ## The least height and rows -/

/-- A carrier state presenting `f` bounds its least height. -/
private theorem leastHeight_le {f : (Fin n → ZMod 2) → ℂ} {T : KernelSumState n}
    (hT : IsCarrier T) (hTf : amp T = f) : leastHeight f ≤ T.h :=
  Nat.sInf_le ⟨T, hT, hTf, rfl⟩

/-- **Attainment.** A function presented by a carrier state is presented at its least height. -/
private theorem exists_leastHeight {f : (Fin n → ZMod 2) → ℂ} {T₀ : KernelSumState n}
    (hT₀ : IsCarrier T₀) (hf : amp T₀ = f) :
    ∃ T : KernelSumState n, IsCarrier T ∧ amp T = f ∧ T.h = leastHeight f :=
  Nat.sInf_mem (s := {h : ℕ | ∃ T : KernelSumState n, IsCarrier T ∧ amp T = f ∧ T.h = h})
    ⟨T₀.h, T₀, hT₀, hf, rfl⟩

/-- **The least height is arithmetic on rows.** For a function presented by a carrier state, rows
of `2 ^ h` phases exist exactly at the heights from the least height on. -/
private theorem hasRowSums_iff_leastHeight_le {f : (Fin n → ZMod 2) → ℂ} {T₀ : KernelSumState n}
    (hT₀ : IsCarrier T₀) (hf : amp T₀ = f) (h : ℕ) :
    (∃ r, HasRowSums f h r) ↔ leastHeight f ≤ h := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨T, hT, hTf, hTh, -⟩ := exists_isCarrier_of_hasRowSums (hf ▸ hT₀.2.2.2) hr
    rw [← hTh]
    exact leastHeight_le hT hTf
  · intro hle
    obtain ⟨T, hT, hTf, hTh⟩ := exists_leastHeight hT₀ hf
    have hTle : T.h ≤ h := by rw [hTh]; exact hle
    have hrow := (hasRowSums_amp T).add (h - T.h)
    rw [hTf, Nat.add_sub_cancel' hTle] at hrow
    exact ⟨_, hrow⟩

/-- Rows of a carrier state presenting `f` at its least height. -/
private theorem exists_hasRowSums_leastHeight {f : (Fin n → ZMod 2) → ℂ} {T₀ : KernelSumState n}
    (hT₀ : IsCarrier T₀) (hf : amp T₀ = f) : ∃ r, HasRowSums f (leastHeight f) r :=
  (hasRowSums_iff_leastHeight_le hT₀ hf _).mpr le_rfl

/-! ## The statement -/

/-- **The least height presenting controlled-H's output.** For a carrier state `S` at any height and
any precision, distinct free bits `c ≠ t`, and the controlled-H word run at any precision `k` at
least three and at least `S.m`, with `f = controlledHAmp c t (amp S)`:

1. a carrier state of height `h` in the `StateEq` class of the word's output exists exactly when
   `leastHeight f ≤ h`;
2. `f` has rows of `2 ^ h` phases at some scale exactly when `leastHeight f ≤ h`;
3. a carrier state of height `h` related to the word's output by the equivalence `CarrierRule`
   generates exists exactly when `f` has rows of `2 ^ h` phases at a scale whose ratio to `S.c` is
   dyadic;
4. `leastHeight f` and `leastHeight (amp S)` differ by at most one. -/
theorem leastHeight_controlledH {S : KernelSumState n} (hS : IsCarrier S) {c t : Fin n}
    (hct : c ≠ t) (k : ℕ) (hmk : S.m ≤ k) (hk : 3 ≤ k) :
    (∀ h : ℕ, (∃ T : KernelSumState n, IsCarrier T ∧ T.h = h
        ∧ StateEq T (run (controlledHWord k hk hct) (liftPrecision S k hmk)))
      ↔ leastHeight (controlledHAmp c t (amp S)) ≤ h)
    ∧ (∀ h : ℕ, (∃ r : ℂ, HasRowSums (controlledHAmp c t (amp S)) h r)
      ↔ leastHeight (controlledHAmp c t (amp S)) ≤ h)
    ∧ (∀ h : ℕ, (∃ T : KernelSumState n, IsCarrier T ∧ T.h = h
        ∧ Relation.EqvGen CarrierRule (run (controlledHWord k hk hct) (liftPrecision S k hmk)) T)
      ↔ ∃ r : ℂ, IsDyadicRatio (r / S.c) ∧ HasRowSums (controlledHAmp c t (amp S)) h r)
    ∧ leastHeight (controlledHAmp c t (amp S)) ≤ leastHeight (amp S) + 1
    ∧ leastHeight (amp S) ≤ leastHeight (controlledHAmp c t (amp S)) + 1 := by
  obtain ⟨hW, hWamp⟩ := amp_controlledHWord hS hct k hmk hk
  have hf0 : controlledHAmp c t (amp S) ≠ 0 := hWamp ▸ hW.2.2.2
  have hrowIff := hasRowSums_iff_leastHeight_le hW hWamp
  refine ⟨fun h => ⟨?_, fun hle => ?_⟩, hrowIff, fun h => ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨T, hT, rfl, hTW⟩
    exact leastHeight_le hT (Eq.trans hTW hWamp)
  · obtain ⟨r, hr⟩ := (hrowIff h).mpr hle
    obtain ⟨T, hT, hTf, hTh, -⟩ := exists_isCarrier_of_hasRowSums hf0 hr
    exact ⟨T, hT, hTh, hTf.trans hWamp.symm⟩
  · rintro ⟨T, hT, rfl, hWT⟩
    obtain ⟨hst, hdy⟩ := (rewrite_complete hW hT).mp hWT
    obtain ⟨e, he⟩ := exists_c_run (controlledHWord k hk hct) (liftPrecision S k hmk)
    have hr := hasRowSums_amp T
    have hTf : amp T = controlledHAmp c t (amp S) := Eq.trans (Eq.symm hst) hWamp
    rw [← hTf]
    refine ⟨T.c / (Real.sqrt 2 : ℂ) ^ T.h, ?_, hr⟩
    have hratio : T.c / (Real.sqrt 2 : ℂ) ^ T.h / S.c
        = T.c / (run (controlledHWord k hk hct) (liftPrecision S k hmk)).c
          * (Real.sqrt 2 : ℂ) ^ (-((e + T.h : ℕ) : ℤ)) := by
      rw [he, zpow_neg, zpow_natCast, pow_add]
      have hSc := c_ne_zero_of_isCarrier hS
      have hs := ofReal_sqrt_two_ne_zero
      change T.c / (Real.sqrt 2 : ℂ) ^ T.h / S.c
        = T.c / (S.c / (Real.sqrt 2 : ℂ) ^ e) * ((Real.sqrt 2 : ℂ) ^ e * (Real.sqrt 2 : ℂ) ^ T.h)⁻¹
      field_simp
    rw [hratio]
    exact hdy.mul (isDyadicRatio_sqrt_two_zpow _)
  · rintro ⟨r, hdy, hr⟩
    obtain ⟨T, hT, hTf, hTh, hTc⟩ := exists_isCarrier_of_hasRowSums hf0 hr
    obtain ⟨e, he⟩ := exists_c_run (controlledHWord k hk hct) (liftPrecision S k hmk)
    refine ⟨T, hT, hTh, (rewrite_complete hW hT).mpr ⟨hWamp.trans hTf.symm, ?_⟩⟩
    have hratio : T.c / (run (controlledHWord k hk hct) (liftPrecision S k hmk)).c
        = r / S.c * (Real.sqrt 2 : ℂ) ^ ((h + e : ℕ) : ℤ) := by
      rw [hTc, he, zpow_natCast, pow_add]
      have hSc := c_ne_zero_of_isCarrier hS
      have hs := ofReal_sqrt_two_ne_zero
      change r * (Real.sqrt 2 : ℂ) ^ h / (S.c / (Real.sqrt 2 : ℂ) ^ e)
        = r / S.c * ((Real.sqrt 2 : ℂ) ^ h * (Real.sqrt 2 : ℂ) ^ e)
      field_simp
    rw [hratio]
    exact hdy.mul (isDyadicRatio_sqrt_two_zpow _)
  · obtain ⟨r, hr⟩ := exists_hasRowSums_leastHeight hS rfl
    obtain ⟨r', hr'⟩ := hr.controlledH c t
    exact (hrowIff _).mp ⟨r', hr'⟩
  · obtain ⟨r, hr⟩ := exists_hasRowSums_leastHeight hW hWamp
    obtain ⟨r', hr'⟩ := hr.controlledH c t
    rw [controlledHAmp_involutive hct] at hr'
    exact (hasRowSums_iff_leastHeight_le hS rfl _).mp ⟨r', hr'⟩

end FTQCLib.Frame.Walkthrough

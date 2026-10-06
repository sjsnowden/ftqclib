/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.CarrierClifford
import FTQCLib.Carrier.CarrierStateHadamard

/-!
# Gate words on carrier registers at any height

A **gate word** is a list of letters: H on a free bit, a diagonal gate given by any phase
polynomial at the word's precision, and CNOT between two distinct free bits (`GateLetter`,
`GateWord`). A word runs on a carrier state of any height (`run`), head letter first, and the
statement of this module (`docs/TARGETS.md`, T05) is that on a carrier state at the word's
precision the run's amplitude is the composite of the letters' referees (`amp_run`) and the run
keeps the carrier property (`isCarrier_run`). The referees are those decision D5 names: the Walsh
transform for H, multiplication by the phase for a diagonal gate, the CNOT permutation for CNOT
(`letterAmp`, `runAmp`).

This is the word type phase 2's protocol syntax builds on (T13's feed-forward, T14's protocols),
so its letters are exactly the gates and nothing is threaded beside the word: a diagonal letter
takes any exponent, and CNOT carries the distinctness of its bits as part of the letter, so every
word is a circuit and no well-formedness predicate is needed. The precision is an index of the
letter type, as it is of `NormalGate`, because a diagonal exponent lives at one precision; the one
case outside every theorem is a diagonal letter met by a carrier state at another precision, which
`applyLetter` leaves unchanged (the hypothesis `S.m = m` of `amp_run` and `isCarrier_run` names
it, as it does for `runNormal_floor`).

**H at any height.** The two constructors of the covering theorem `hadamard_cover` are the free
rule `applyHFiner` (the bit is X-supported; one bound bit is adjoined) and the representer rule
`hRaise` (it is not; the support turns and no bound bit is adjoined). `applyH` chooses by the data
`hRaise` consumes: when a representer exists it is used (chosen, as gauge R6 allows); when none
does, the free rule. On a carrier state this is the dichotomy `hadamard_dichotomy`, so `applyH`
computes the Walsh transform (`amp_applyH`) and keeps the carrier property (`isCarrier_applyH`).

**What the run keeps and what it does not.** The precision (`run_m`) and the carrier property
(`isCarrier_run`); not the height, which grows by one at each free-rule H, and not the floor: this
run never eliminates. The floor runner `runNormal` of `CliffordWordFloor.lean` is the height-zero
Clifford specialization, whose H eliminates and whose diagonal letter shears the Lagrangian; on a
floor the two runs agree in amplitude on words whose letters have the same referees, letter by
letter. That is a row of the check module (`GateWordCheck.lean`, `amp_runNormal_eq_amp_run`), not
a theorem here, since this module does not import `CliffordWordFloor.lean`.

Everything here is frame-pure. No `FTQCLib.Hilbert`.

## Main definitions

* `GateLetter`, `GateWord` — the letters `hadamard k | diagonal D | cnot i j hij` at precision
  `m`, and words of them.
* `letterAmp`, `runAmp` — the referee of a letter and of a word, on amplitude functions.
* `applyH` — H on a free bit at any height, by the two constructors of `hadamard_cover`.
* `applyLetter`, `run` — a letter and a word on a carrier state.

## Main results

* `amp_run` — on a carrier state at the word's precision, the run's amplitude is the referee's
  (proved at T05.3.2).
* `isCarrier_run` — the run keeps the carrier property (T05.3.3).
* `isCarrier_applyDiagSum` — the diagonal rule keeps the carrier property at every height
  (T05.3.1). It is stated here and not beside `applyDiagSum`, since `IsCarrier` is defined above
  `CharSumGates.lean` in the import order.
* `amp_applyH`, `isCarrier_applyH` — the H letter's referee and carrier closure, from the
  covering theorem.
* `amp_applyLetter`, `isCarrier_applyLetter` — one letter at the state's own precision: its
  referee and carrier closure, the step of the two inductions above, public for T13's and T14's
  inductions over words with conditioning letters between them.
* `sum_normSq_letterAmp`, `sum_normSq_runAmp` — a letter's and a word's referee keep
  `Σ_w |·|²`: the Walsh transform is an isometry, a phase has modulus one, a CNOT permutes words.

Made public here from `UnreadBits.lean`, their one home (docs/STEPS.md, entry 2026-10-01n):

* `runAmp_add_smul`, `innerSum_runAmp` — a word's referee is linear and keeps the inner sums
  `innerSum a b = Σ_u a(u)·conj(b(u))`.
* `padZero`, `invWord`, `widenLetter` with `runAmp_invWord`, `runAmp_widenWord` — the zero
  padding of a function to more bits; the inverse word undoes the word; a word widened to more
  bits acts on a padded function as the word, padded.
* `Realizes`, `exists_realizes_perm`, `realizes_flip`, `exists_realizes_xor`,
  `exists_realizes_insertLast` — words at precision one realise every permutation of the bits, a
  flip, and the addition to one bit of a sum of the others.

## Implementation notes

* `amp_run` is stated on `IsCarrier`, the glossary's carrier, although its proof uses of it only
  the positive precision and the Lagrangian: the H referee needs the dichotomy, which needs the
  Lagrangian, and nothing needs the nonzero amplitude. The stronger hypothesis is the statement's
  subject, a carrier state, and keeps one predicate along the run.
* The run is `List.foldl`, head letter first, as `runNormal` is; `run_cons` and `run_append` are
  the equations an induction over a protocol needs.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The letters and the referee -/

/-- A letter at precision `m`: H on a free bit, a diagonal gate given by any exponent at precision
`m`, CNOT with control `i` and target `j` for distinct `i`, `j`. -/
inductive GateLetter (n m : ℕ) where
  | hadamard : Fin n → GateLetter n m
  | diagonal : DiagPhase n m → GateLetter n m
  | cnot : (i j : Fin n) → i ≠ j → GateLetter n m

/-- A word at precision `m`: a list of letters, run head letter first. -/
abbrev GateWord (n m : ℕ) : Type := List (GateLetter n m)

/-- The referee of a letter on an amplitude function (decision D5): the Walsh transform at the
bit, multiplication by the phase `charOf m (D w)`, precomposition with the CNOT bit-map. -/
noncomputable def letterAmp {m : ℕ} (g : GateLetter n m) (f : (Fin n → ZMod 2) → ℂ) :
    (Fin n → ZMod 2) → ℂ :=
  match g with
  | .hadamard k => walshTransform k f
  | .diagonal D => fun w => charOf m (D.eval w) * f w
  | .cnot i j _ => fun w => f (cnotBitMap i j w)

/-- The referee of a word, head letter first. -/
noncomputable def runAmp {m : ℕ} (gs : GateWord n m) (f : (Fin n → ZMod 2) → ℂ) :
    (Fin n → ZMod 2) → ℂ :=
  gs.foldl (fun f g => letterAmp g f) f

theorem runAmp_nil {m : ℕ} (f : (Fin n → ZMod 2) → ℂ) : runAmp ([] : GateWord n m) f = f := rfl

theorem runAmp_cons {m : ℕ} (g : GateLetter n m) (gs : GateWord n m)
    (f : (Fin n → ZMod 2) → ℂ) : runAmp (g :: gs) f = runAmp gs (letterAmp g f) := rfl

/-- The referee of a concatenation is the composite, first word first. -/
theorem runAmp_append {m : ℕ} (gs₁ gs₂ : GateWord n m) (f : (Fin n → ZMod 2) → ℂ) :
    runAmp (gs₁ ++ gs₂) f = runAmp gs₂ (runAmp gs₁ f) :=
  List.foldl_append

/-- The CZ letter's phase is `(−1)^{w_i w_j}` at every positive precision. -/
theorem charOf_czGate_eval {m : ℕ} (hm : 1 ≤ m) (i j : Fin n) (w : Fin n → ZMod 2) :
    charOf m ((DiagPhase.czGate m i j).eval w) = (-1 : ℂ) ^ ((w i).val * (w j).val) := by
  rw [DiagPhase.czGate_eval, ← Nat.cast_mul, charOf_two_pow_mul hm]

/-! ## H at any height -/

open Classical in
/-- **H on a free bit at any height.** When a representer of the bit exists (the data `hRaise`
consumes: `u i = 0` and `u` reads the `i`-th coordinate on the shadow) H is the representer rule
with one such `u`; when none does, H is the free rule `applyHFiner`. On a carrier state the two
cases are the dichotomy `hadamard_dichotomy`: a representer exists exactly when the bit is not
X-supported. -/
noncomputable def applyH (i : Fin n) (S : KernelSumState n) : KernelSumState n :=
  if h : ∃ u : Fin n → ZMod 2, u i = 0 ∧ ∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i
  then hRaise i (Classical.choose h) S else applyHFiner i S

/-- The precision is unchanged by H. -/
theorem applyH_m (i : Fin n) (S : KernelSumState n) : (applyH i S).m = S.m := by
  unfold applyH
  split <;> rfl

/-- With a representer, H is the representer rule with some representer. -/
theorem applyH_of_representer (i : Fin n) (S : KernelSumState n)
    (h : ∃ u : Fin n → ZMod 2, u i = 0 ∧ ∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i) :
    ∃ u : Fin n → ZMod 2, u i = 0 ∧ (∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i)
      ∧ applyH i S = hRaise i u S := by
  refine ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
  unfold applyH
  rw [dif_pos h]

/-- Without a representer, H is the free rule. -/
theorem applyH_of_no_representer (i : Fin n) (S : KernelSumState n)
    (h : ¬ ∃ u : Fin n → ZMod 2, u i = 0 ∧ ∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i) :
    applyH i S = applyHFiner i S := by
  unfold applyH
  rw [dif_neg h]

/-- **The cover on a carrier state.** H is the free rule at an X-supported bit and the representer
rule, with a representer, otherwise. -/
theorem applyH_cover {S : KernelSumState n} (hS : IsCarrier S) (i : Fin n) :
    ((Pi.single i 1 : Fin n → ZMod 2) ∈ Submodule.map xProj S.L ∧ applyH i S = applyHFiner i S)
      ∨ ∃ u : Fin n → ZMod 2, u i = 0 ∧ (∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i)
          ∧ applyH i S = hRaise i u S := by
  rcases hadamard_dichotomy hS.2.1 hS.2.2.1 i with ⟨hi, hno⟩ | ⟨hrep, _⟩
  · exact Or.inl ⟨hi, applyH_of_no_representer i S hno⟩
  · exact Or.inr (applyH_of_representer i S hrep)

/-- **The referee of H.** On a carrier state, H computes the Walsh transform at the bit. -/
theorem amp_applyH {S : KernelSumState n} (hS : IsCarrier S) (i : Fin n) :
    amp (applyH i S) = walshTransform i (amp S) := by
  rcases applyH_cover hS i with ⟨hi, heq⟩ | ⟨u, hui, hrep, heq⟩
  · rw [heq]
    exact amp_applyHFiner i S hS.1 hi
  · rw [heq]
    exact amp_hRaise i u S hS.2.2.1 hui hrep hS.1

/-- **Carrier closure of H** at any height. -/
theorem isCarrier_applyH {S : KernelSumState n} (hS : IsCarrier S) (i : Fin n) :
    IsCarrier (applyH i S) := by
  rcases applyH_cover hS i with ⟨hi, heq⟩ | ⟨u, hui, hrep, heq⟩
  · rw [heq]
    exact isCarrier_applyHFiner i hS hi
  · rw [heq]
    exact isCarrier_hRaise i u hS hui hrep

/-! ## The diagonal rule at any height -/

/-- **Carrier closure of the diagonal rule** at any height: the amplitude is multiplied by a phase
and the support is unchanged. Proved at T05.3.1. -/
theorem isCarrier_applyDiagSum {S : KernelSumState n} (hS : IsCarrier S) (D : DiagPhase n S.m) :
    IsCarrier (applyDiagSum S D) := by
  refine ⟨hS.1, hS.2.1, hS.2.2.1, fun hzero => hS.2.2.2 ?_⟩
  funext w
  have hw := congrFun hzero w
  rw [amp_applyDiagSum] at hw
  exact (mul_eq_zero.mp hw).resolve_left (charOf_ne_zero S.m _)

/-! ## Letters and words on a carrier state -/

/-- A letter on a carrier state: H by `applyH`, a diagonal letter by `applyDiagSum` when the
precisions agree (and the state unchanged when they do not: the case outside every theorem),
CNOT by `applyCnotSum`. -/
noncomputable def applyLetter {m : ℕ} (g : GateLetter n m) (S : KernelSumState n) :
    KernelSumState n :=
  match g with
  | .hadamard k => applyH k S
  | .diagonal D => if hm : S.m = m then applyDiagSum S (hm ▸ D) else S
  | .cnot i j _ => applyCnotSum i j S

theorem applyLetter_hadamard {m : ℕ} (k : Fin n) (S : KernelSumState n) :
    applyLetter (GateLetter.hadamard k : GateLetter n m) S = applyH k S := rfl

/-- At the state's own precision a diagonal letter is the diagonal rule. -/
theorem applyLetter_diagonal {S : KernelSumState n} (D : DiagPhase n S.m) :
    applyLetter (GateLetter.diagonal D) S = applyDiagSum S D := by
  change (if hm : S.m = S.m then applyDiagSum S (hm ▸ D) else S) = _
  rw [dif_pos rfl]

theorem applyLetter_cnot {m : ℕ} {i j : Fin n} (hij : i ≠ j) (S : KernelSumState n) :
    applyLetter (GateLetter.cnot i j hij : GateLetter n m) S = applyCnotSum i j S := rfl

/-- Every letter keeps the precision. -/
theorem applyLetter_m {m : ℕ} (g : GateLetter n m) (S : KernelSumState n) :
    (applyLetter g S).m = S.m := by
  cases g with
  | hadamard k => exact applyH_m k S
  | diagonal D =>
    change (if hm : S.m = m then applyDiagSum S (hm ▸ D) else S).m = S.m
    split <;> rfl
  | cnot i j hij => rfl

/-- A word on a carrier state, head letter first. -/
noncomputable def run {m : ℕ} (gs : GateWord n m) (S : KernelSumState n) : KernelSumState n :=
  gs.foldl (fun S g => applyLetter g S) S

theorem run_nil {m : ℕ} (S : KernelSumState n) : run ([] : GateWord n m) S = S := rfl

theorem run_cons {m : ℕ} (g : GateLetter n m) (gs : GateWord n m) (S : KernelSumState n) :
    run (g :: gs) S = run gs (applyLetter g S) := rfl

/-- The run of a concatenation is the composite, first word first. -/
theorem run_append {m : ℕ} (gs₁ gs₂ : GateWord n m) (S : KernelSumState n) :
    run (gs₁ ++ gs₂) S = run gs₂ (run gs₁ S) :=
  List.foldl_append

/-- The run keeps the precision. -/
theorem run_m {m : ℕ} (gs : GateWord n m) (S : KernelSumState n) : (run gs S).m = S.m := by
  induction gs generalizing S with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih, applyLetter_m]

/-! ## The statement -/

/-- A letter at the state's own precision keeps the carrier property: the three constructors read
off `isCarrier_applyH`, `isCarrier_applyDiagSum` (with the precisions identified by `hm`) and
`isCarrier_applyCnotSum`. -/
theorem isCarrier_applyLetter {m : ℕ} (g : GateLetter n m) {S : KernelSumState n}
    (hS : IsCarrier S) (hm : S.m = m) : IsCarrier (applyLetter g S) := by
  subst hm
  cases g with
  | hadamard k => rw [applyLetter_hadamard]; exact isCarrier_applyH hS k
  | diagonal D => rw [applyLetter_diagonal]; exact isCarrier_applyDiagSum hS D
  | cnot i j hij => rw [applyLetter_cnot]; exact isCarrier_applyCnotSum hij hS

/-- A letter at the state's own precision has the referee's amplitude: the three constructors read
off `amp_applyH`, `amp_applyDiagSum` (with the precisions identified by `hm`) and
`amp_applyCnotSum`, each matching `letterAmp`'s own case by definitional unfolding. -/
theorem amp_applyLetter {m : ℕ} (g : GateLetter n m) {S : KernelSumState n}
    (hS : IsCarrier S) (hm : S.m = m) : amp (applyLetter g S) = letterAmp g (amp S) := by
  subst hm
  cases g with
  | hadamard k => rw [applyLetter_hadamard]; exact amp_applyH hS k
  | diagonal D => rw [applyLetter_diagonal]; exact amp_applyDiagSum S D
  | cnot i j hij => rw [applyLetter_cnot]; exact amp_applyCnotSum hij S

/-- **The amplitude theorem.** On a carrier state at the word's precision, the run's amplitude is
the composite of the letters' referees: the Walsh transform for H, multiplication by the phase for
a diagonal letter, the CNOT permutation for CNOT. Induction on the word: the empty word is
`run_nil`/`runAmp_nil`; a head letter `g` keeps the precision (`applyLetter_m`) and the carrier
property and referee agreement (`isCarrier_applyLetter`, `amp_applyLetter`), so the tail's run
composes by the induction hypothesis. Proved at T05.3.2. -/
theorem amp_run {m : ℕ} (gs : GateWord n m) {S : KernelSumState n} (hS : IsCarrier S)
    (hm : S.m = m) : amp (run gs S) = runAmp gs (amp S) := by
  induction gs generalizing S hS hm with
  | nil => rw [run_nil, runAmp_nil]
  | cons g gs ih =>
    rw [run_cons, runAmp_cons, ← amp_applyLetter g hS hm]
    exact ih (isCarrier_applyLetter g hS hm) ((applyLetter_m g S).trans hm)

/-- **Carrier preservation along the run.** A word at the precision of a carrier state runs to a
carrier state. Proved at T05.3.3. -/
theorem isCarrier_run {m : ℕ} (gs : GateWord n m) {S : KernelSumState n} (hS : IsCarrier S)
    (hm : S.m = m) : IsCarrier (run gs S) := by
  induction gs generalizing S hS hm with
  | nil => rw [run_nil]; exact hS
  | cons g gs ih =>
    rw [run_cons]
    exact ih (isCarrier_applyLetter g hS hm) ((applyLetter_m g S).trans hm)

/-! ## The referee keeps the squared norm -/

/-- One letter keeps `Σ_w |·|²`: the Walsh transform is an isometry, a phase has modulus one, and
the CNOT bit-map is a bijection of the words. -/
theorem sum_normSq_letterAmp {N m : ℕ} (g : GateLetter N m) (f : (Fin N → ZMod 2) → ℂ) :
    ∑ w : Fin N → ZMod 2, Complex.normSq (letterAmp g f w)
      = ∑ w : Fin N → ZMod 2, Complex.normSq (f w) := by
  cases g with
  | hadamard k => exact walsh_normSq_isometry k f
  | diagonal D =>
    refine Finset.sum_congr rfl fun w _ => ?_
    change Complex.normSq (charOf m (D.eval w) * f w) = _
    rw [map_mul]
    unfold charOf
    rw [normSq_exp_I_real, one_mul]
  | cnot i j hij =>
    exact Fintype.sum_equiv (Function.Involutive.toPerm _ (cnotBitMap_involutive i j hij))
      _ (fun w => Complex.normSq (f w)) (fun _ => rfl)

/-- A word keeps `Σ_w |·|²`, letter by letter. -/
theorem sum_normSq_runAmp {N m : ℕ} (gs : GateWord N m) (f : (Fin N → ZMod 2) → ℂ) :
    ∑ w : Fin N → ZMod 2, Complex.normSq (runAmp gs f w)
      = ∑ w : Fin N → ZMod 2, Complex.normSq (f w) := by
  induction gs generalizing f with
  | nil => rfl
  | cons g gs ih => rw [runAmp_cons, ih, sum_normSq_letterAmp]

/-! ## Linearity and inner sums (docs/STEPS.md, entry 2026-10-01n) -/

/-- The inner sum `Σ_u a(u) · conj (b(u))` of two functions on a finite type: the Gram data at
`(x, y)` is the inner sum of the unread vectors at `x` and `y` (`gram_eq_innerSum`). -/
noncomputable def innerSum {α : Type*} [Fintype α] (a b : α → ℂ) : ℂ :=
  ∑ u, a u * starRingEnd ℂ (b u)

/-- An inner sum of a function with itself is the sum of the squared moduli. -/
theorem innerSum_self {α : Type*} [Fintype α] (a : α → ℂ) :
    innerSum a a = ((∑ u, Complex.normSq (a u) : ℝ) : ℂ) := by
  unfold innerSum
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun u _ => Complex.mul_conj (a u)

/-- The expansion of `⟨a + c b, a + c b⟩`, the step of the polarization in `innerSum_runAmp`. -/
theorem innerSum_add_smul_self {α : Type*} [Fintype α] (a b : α → ℂ) (c : ℂ) :
    innerSum (a + c • b) (a + c • b)
      = innerSum a a + starRingEnd ℂ c * innerSum a b + c * innerSum b a
        + c * starRingEnd ℂ c * innerSum b b := by
  unfold innerSum
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

/-- One letter's referee is linear: `letterAmp g (a + c b) = letterAmp g a + c · letterAmp g b`. -/
theorem letterAmp_add_smul {N m : ℕ} (g : GateLetter N m) (a b : (Fin N → ZMod 2) → ℂ)
    (c : ℂ) : letterAmp g (a + c • b) = letterAmp g a + c • letterAmp g b := by
  funext w
  cases g with
  | hadamard i =>
    change walshTransform i (a + c • b) w = walshTransform i a w + c * walshTransform i b w
    unfold walshTransform
    rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  | diagonal D =>
    change charOf m (D.eval w) * (a w + c * b w)
      = charOf m (D.eval w) * a w + c * (charOf m (D.eval w) * b w)
    ring
  | cnot i j hij => rfl

/-- A word's referee is linear, letter by letter. -/
theorem runAmp_add_smul {N m : ℕ} (W : GateWord N m) (a b : (Fin N → ZMod 2) → ℂ)
    (c : ℂ) : runAmp W (a + c • b) = runAmp W a + c • runAmp W b := by
  induction W generalizing a b with
  | nil => rfl
  | cons g gs ih => rw [runAmp_cons, runAmp_cons, runAmp_cons, letterAmp_add_smul, ih]

/-- **A word's referee keeps the inner sums.** It is linear (`runAmp_add_smul`) and keeps
`Σ |·|²` (`sum_normSq_runAmp`); polarization at `a + b` and `a + i b` recovers `⟨a, b⟩`. -/
theorem innerSum_runAmp {N m : ℕ} (W : GateWord N m) (a b : (Fin N → ZMod 2) → ℂ) :
    innerSum (runAmp W a) (runAmp W b) = innerSum a b := by
  have hnorm : ∀ f : (Fin N → ZMod 2) → ℂ,
      innerSum (runAmp W f) (runAmp W f) = innerSum f f :=
    fun f => by rw [innerSum_self, innerSum_self, sum_normSq_runAmp]
  have hone := hnorm (a + (1 : ℂ) • b)
  have hI := hnorm (a + Complex.I • b)
  rw [runAmp_add_smul, innerSum_add_smul_self, innerSum_add_smul_self, hnorm a, hnorm b] at hone hI
  rw [map_one] at hone
  rw [Complex.conj_I] at hI
  linear_combination (1 / 2 : ℂ) * hone + (Complex.I / 2) * hI
    + ((innerSum (runAmp W a) (runAmp W b) - innerSum a b
      - (innerSum (runAmp W b) (runAmp W a) - innerSum b a)) / 2) * Complex.I_sq

/-! ## Zero padding, inverse words and words on more bits -/

/-- The zero padding of a function on `k` bits to `N ≥ k` bits: `φ` on the first `k` bits, and
zero unless every later bit is zero. -/
noncomputable def padZero {k N : ℕ} (hk : k ≤ N) (φ : (Fin k → ZMod 2) → ℂ) :
    (Fin N → ZMod 2) → ℂ :=
  fun v => if ∀ i : Fin N, k ≤ i.val → v i = 0 then φ fun i => v (Fin.castLE hk i) else 0

/-- Padding to the same count is the identity. -/
theorem padZero_self {k : ℕ} (hk : k ≤ k) (φ : (Fin k → ZMod 2) → ℂ) :
    padZero hk φ = φ := by
  funext v
  have hall : ∀ i : Fin k, k ≤ i.val → v i = 0 := fun i hi => absurd i.isLt (by omega)
  unfold padZero
  rw [if_pos hall]
  rfl

/-- Padding twice is padding once. -/
theorem padZero_padZero {k N₁ N : ℕ} (hk : k ≤ N₁) (hN : N₁ ≤ N)
    (φ : (Fin k → ZMod 2) → ℂ) : padZero hN (padZero hk φ) = padZero (hk.trans hN) φ := by
  funext v
  unfold padZero
  by_cases h₁ : ∀ i : Fin N, N₁ ≤ i.val → v i = 0
  · rw [if_pos h₁]
    by_cases h₂ : ∀ i : Fin N₁, k ≤ i.val → v (Fin.castLE hN i) = 0
    · have h₃ : ∀ i : Fin N, k ≤ i.val → v i = 0 := by
        intro i hi
        by_cases hiN : i.val < N₁
        · exact h₂ ⟨i.val, hiN⟩ hi
        · exact h₁ i (by omega)
      rw [if_pos h₂, if_pos h₃]
      rfl
    · have h₃ : ¬ ∀ i : Fin N, k ≤ i.val → v i = 0 := fun h => h₂ fun i hi => h _ hi
      rw [if_neg h₂, if_neg h₃]
  · have h₃ : ¬ ∀ i : Fin N, k ≤ i.val → v i = 0 :=
      fun h => h₁ fun i hi => h i (by omega)
    rw [if_neg h₁, if_neg h₃]

/-- Updating a bit below the padding commutes with the padding. -/
theorem padZero_update {N₁ N : ℕ} (hN : N₁ ≤ N) (ψ : (Fin N₁ → ZMod 2) → ℂ)
    (v : Fin N → ZMod 2) (p : Fin N₁) (b : ZMod 2) :
    padZero hN ψ (Function.update v (Fin.castLE hN p) b)
      = if ∀ i : Fin N, N₁ ≤ i.val → v i = 0
        then ψ (Function.update (fun i => v (Fin.castLE hN i)) p b) else 0 := by
  have hcond : (∀ i : Fin N, N₁ ≤ i.val → Function.update v (Fin.castLE hN p) b i = 0)
      ↔ ∀ i : Fin N, N₁ ≤ i.val → v i = 0 := by
    have hne : ∀ i : Fin N, N₁ ≤ i.val → i ≠ Fin.castLE hN p := by
      intro i hi he
      have hval := congrArg Fin.val he
      rw [Fin.val_castLE] at hval
      have := p.isLt
      omega
    refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
    · have := h i hi
      rwa [Function.update_of_ne (hne i hi)] at this
    · rw [Function.update_of_ne (hne i hi)]
      exact h i hi
  have hcomp : (fun i => Function.update v (Fin.castLE hN p) b (Fin.castLE hN i))
      = Function.update (fun i => v (Fin.castLE hN i)) p b :=
    Function.update_comp_eq_of_injective v (Fin.castLE_injective hN) p b
  unfold padZero
  rw [hcomp]
  by_cases h : ∀ i : Fin N, N₁ ≤ i.val → v i = 0
  · rw [if_pos (hcond.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hcond.mp h')), if_neg h]

/-- The inverse letter: H and CNOT are their own inverses, a diagonal letter's inverse negates its
exponent. -/
noncomputable def invLetter {N M : ℕ} : GateLetter N M → GateLetter N M
  | .hadamard i => .hadamard i
  | .diagonal D => .diagonal (-D)
  | .cnot i j hij => .cnot i j hij

/-- The inverse letter undoes the letter. -/
theorem letterAmp_invLetter {N M : ℕ} (g : GateLetter N M)
    (f : (Fin N → ZMod 2) → ℂ) : letterAmp (invLetter g) (letterAmp g f) = f := by
  cases g with
  | hadamard i => exact walshTransform_involutive i f
  | diagonal D =>
    funext w
    change charOf M (DiagPhase.eval (-D) w) * (charOf M (DiagPhase.eval D w) * f w) = f w
    rw [DiagPhase.eval, DiagPhase.eval, map_neg, charOf_neg, ← mul_assoc,
      inv_mul_cancel₀ (charOf_ne_zero M _), one_mul]
  | cnot i j hij =>
    funext w
    exact congrArg f (cnotBitMap_involutive i j hij w)

/-- The inverse word: the inverse letters in reverse order. -/
noncomputable def invWord {N M : ℕ} (W : GateWord N M) : GateWord N M :=
  (W.map invLetter).reverse

/-- The inverse word undoes the word. -/
theorem runAmp_invWord {N M : ℕ} (W : GateWord N M) (f : (Fin N → ZMod 2) → ℂ) :
    runAmp (invWord W) (runAmp W f) = f := by
  induction W generalizing f with
  | nil => rfl
  | cons g gs ih =>
    have hgs := ih (letterAmp g f)
    rw [invWord] at hgs
    rw [invWord, List.map_cons, List.reverse_cons, runAmp_append, runAmp_cons g gs f, hgs]
    exact letterAmp_invLetter g f

/-- A letter on `N₁` bits, read on `N ≥ N₁` bits at the first `N₁`. -/
noncomputable def widenLetter {N₁ N M : ℕ} (hN : N₁ ≤ N) :
    GateLetter N₁ M → GateLetter N M
  | .hadamard i => .hadamard (Fin.castLE hN i)
  | .diagonal D => .diagonal (MvPolynomial.rename (Fin.castLE hN) D)
  | .cnot i j hij => .cnot (Fin.castLE hN i) (Fin.castLE hN j)
      fun h => hij (Fin.castLE_injective hN h)

/-- A widened letter acts on a padded function as the letter on the function, padded. -/
theorem letterAmp_widenLetter {N₁ N M : ℕ} (hN : N₁ ≤ N) (g : GateLetter N₁ M)
    (ψ : (Fin N₁ → ZMod 2) → ℂ) :
    letterAmp (widenLetter hN g) (padZero hN ψ) = padZero hN (letterAmp g ψ) := by
  funext v
  cases g with
  | hadamard i =>
    change walshTransform (Fin.castLE hN i) (padZero hN ψ) v
      = padZero hN (walshTransform i ψ) v
    unfold walshTransform
    rw [padZero_update, padZero_update]
    unfold padZero
    by_cases h : ∀ i : Fin N, N₁ ≤ i.val → v i = 0
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg h, mul_zero, add_zero, mul_zero]
  | diagonal D =>
    change charOf M (DiagPhase.eval (MvPolynomial.rename (Fin.castLE hN) D) v) * padZero hN ψ v
      = padZero hN (fun w => charOf M (DiagPhase.eval D w) * ψ w) v
    rw [DiagPhase.eval, MvPolynomial.eval_rename]
    unfold padZero
    by_cases h : ∀ i : Fin N, N₁ ≤ i.val → v i = 0
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h, mul_zero]
  | cnot i j hij =>
    change padZero hN ψ (DiagPhase.cnotBitMap (Fin.castLE hN i) (Fin.castLE hN j) v)
      = padZero hN (fun w => ψ (DiagPhase.cnotBitMap i j w)) v
    unfold DiagPhase.cnotBitMap
    rw [padZero_update]
    unfold padZero
    split_ifs <;> rfl

/-- A widened word acts on a padded function as the word on the function, padded. -/
theorem runAmp_widenWord {N₁ N M : ℕ} (hN : N₁ ≤ N) (W : GateWord N₁ M)
    (ψ : (Fin N₁ → ZMod 2) → ℂ) :
    runAmp (W.map (widenLetter hN)) (padZero hN ψ) = padZero hN (runAmp W ψ) := by
  induction W generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    change runAmp (gs.map (widenLetter hN)) (letterAmp (widenLetter hN g) (padZero hN ψ)) = _
    rw [letterAmp_widenLetter, ih]
    rfl

/-! ## Words that permute and flip bits -/

/-- A word at precision one realises a map `A` of the words when its referee is precomposition
with `A`. -/
def Realizes {N : ℕ} (W : GateWord N 1) (A : (Fin N → ZMod 2) → Fin N → ZMod 2) : Prop :=
  ∀ ψ : (Fin N → ZMod 2) → ℂ, runAmp W ψ = fun v => ψ (A v)

/-- Concatenation composes the realised maps, the second word's map applied first. -/
theorem Realizes.append {N : ℕ} {W₁ W₂ : GateWord N 1}
    {A₁ A₂ : (Fin N → ZMod 2) → Fin N → ZMod 2} (h₁ : Realizes W₁ A₁)
    (h₂ : Realizes W₂ A₂) :
    Realizes (W₁ ++ W₂) fun v => A₁ (A₂ v) := by
  intro ψ
  rw [runAmp_append, h₁, h₂]

/-- Three CNOTs swap two bits. -/
theorem realizes_swap {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Realizes [.cnot i j hij, .cnot j i hij.symm, .cnot i j hij]
      fun v => v ∘ Equiv.swap i j := by
  intro ψ
  funext v
  change ψ (DiagPhase.cnotBitMap i j (DiagPhase.cnotBitMap j i (DiagPhase.cnotBitMap i j v)))
    = ψ (v ∘ Equiv.swap i j)
  congr 1
  funext l
  unfold DiagPhase.cnotBitMap
  have hxor : ∀ a b : ZMod 2, a + (b + a) = b ∧ b + a + (a + (b + a)) = a := by decide
  by_cases hli : l = i
  · subst hli
    simp only [Function.comp_apply, Equiv.swap_apply_left, Function.update_self,
      Function.update_of_ne hij, Function.update_of_ne hij.symm]
    exact (hxor (v l) (v j)).1
  · by_cases hlj : l = j
    · subst hlj
      simp only [Function.comp_apply, Equiv.swap_apply_right, Function.update_self,
        Function.update_of_ne hij, Function.update_of_ne hij.symm]
      exact (hxor (v i) (v l)).2
    · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hli hlj, Function.update_of_ne hlj,
        Function.update_of_ne hli, Function.update_of_ne hlj]

/-- Every permutation of the bits is realised by a CNOT word. -/
theorem exists_realizes_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ∃ W : GateWord N 1, Realizes W fun v => v ∘ σ := by
  refine Equiv.Perm.swap_induction_on σ ⟨[], fun ψ => rfl⟩ ?_
  rintro τ x y hxy ⟨W, hW⟩
  refine ⟨W ++ [.cnot x y hxy, .cnot y x hxy.symm, .cnot x y hxy], fun ψ => ?_⟩
  rw [(hW.append (realizes_swap x y hxy)) ψ]
  rfl

/-- The character of a bit at precision one is its sign. -/
private theorem charOf_one_val (b : ZMod 2) :
    charOf 1 (((b.val : ℕ) : ZMod (2 ^ 1))) = signOf b := by
  have h := charOf_two_pow_mul (m := 1) le_rfl b.val
  rw [Nat.sub_self, pow_zero, one_mul] at h
  rw [h]
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) b with rfl | rfl
  · rw [ZMod.val_zero, pow_zero]
    exact (if_pos rfl).symm
  · rw [ZMod.val_one, pow_one, signOf_one]

/-- X on bit `j`, as H, Z, H at precision one. -/
theorem realizes_flip {N : ℕ} (j : Fin N) :
    Realizes [.hadamard j, .diagonal (MvPolynomial.X j), .hadamard j]
      fun v => Function.update v j (v j + 1) := by
  intro ψ
  funext v
  have hZ : ∀ w : Fin N → ZMod 2,
      charOf 1 (DiagPhase.eval (MvPolynomial.X j : DiagPhase N 1) w) = signOf (w j) := by
    intro w
    rw [DiagPhase.eval, MvPolynomial.eval_X]
    exact charOf_one_val (w j)
  change walshTransform j (fun w => charOf 1 (DiagPhase.eval (MvPolynomial.X j) w)
      * walshTransform j ψ w) v = ψ (Function.update v j (v j + 1))
  unfold walshTransform
  beta_reduce
  rw [hZ, hZ]
  simp only [Function.update_self, Function.update_idem]
  have h0 : signOf 0 = 1 := if_pos rfl
  have ht : (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
    rw [one_div_mul_one_div, ← sq, sqrt_two_sq_complex]
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (v j) with hv | hv
  · rw [hv, zero_add, h0, signOf_one]
    linear_combination (2 * ψ (Function.update v j 1)) * ht
  · rw [hv, show (1 : ZMod 2) + 1 = 0 by decide, h0, signOf_one]
    linear_combination (2 * ψ (Function.update v j 0)) * ht

/-- Adding a constant to bit `j` is realised: the empty word or X. -/
theorem exists_realizes_add {N : ℕ} (j : Fin N) (c : ZMod 2) :
    ∃ W : GateWord N 1, Realizes W fun v => Function.update v j (v j + c) := by
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) c with rfl | rfl
  · refine ⟨[], fun ψ => ?_⟩
    funext v
    change ψ v = ψ (Function.update v j (v j + 0))
    rw [add_zero, Function.update_eq_self]
  · exact ⟨_, realizes_flip j⟩

/-- Adding to bit `j` a sum of the other bits is realised by CNOTs into `j`. -/
theorem exists_realizes_xor {N : ℕ} (j : Fin (N + 1)) (g : Fin N → ZMod 2)
    (s : Finset (Fin N)) :
    ∃ W : GateWord (N + 1) 1, Realizes W fun v =>
      Function.update v j (v j + ∑ i ∈ s, g i * v (j.succAbove i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨[], fun ψ => ?_⟩
    funext v
    change ψ v
      = ψ (Function.update v j (v j + ∑ i ∈ (∅ : Finset (Fin N)), g i * v (j.succAbove i)))
    rw [Finset.sum_empty, add_zero, Function.update_eq_self]
  | insert i s hi ih =>
    obtain ⟨W, hW⟩ := ih
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (g i) with hg | hg
    · refine ⟨W, fun ψ => ?_⟩
      rw [hW ψ]
      funext v
      beta_reduce
      rw [Finset.sum_insert hi, hg, zero_mul, zero_add]
    · refine ⟨W ++ [.cnot (j.succAbove i) j (Fin.succAbove_ne j i)], fun ψ => ?_⟩
      rw [(hW.append fun _ => rfl) ψ]
      funext v
      congr 1
      beta_reduce
      unfold DiagPhase.cnotBitMap
      have hsum : ∑ l ∈ s, g l * Function.update v j (v j + v (j.succAbove i)) (j.succAbove l)
          = ∑ l ∈ s, g l * v (j.succAbove l) :=
        Finset.sum_congr rfl fun l _ => by rw [Function.update_of_ne (Fin.succAbove_ne j l)]
      rw [Function.update_self, Function.update_idem, hsum, Finset.sum_insert hi, hg, one_mul,
        add_assoc]

/-- Moving the last bit to position `j`, the others in order, is realised by a CNOT word. -/
theorem exists_realizes_insertLast {k : ℕ} (j : Fin (k + 1)) :
    ∃ W : GateWord (k + 1) 1, Realizes W fun v =>
      (Fin.insertNth j (v (Fin.last k)) (Fin.init v) : Fin (k + 1) → ZMod 2) := by
  obtain ⟨W, hW⟩ :=
    exists_realizes_perm ((finSuccEquiv' j).trans (finSuccEquiv' (Fin.last k)).symm)
  refine ⟨W, fun ψ => ?_⟩
  rw [hW ψ]
  funext v
  congr 1
  funext l
  beta_reduce
  rcases Fin.eq_self_or_eq_succAbove j l with rfl | ⟨i, rfl⟩
  · rw [Fin.insertNth_apply_same, Function.comp_apply, Equiv.trans_apply, finSuccEquiv'_at,
      finSuccEquiv'_symm_none]
  · rw [Fin.insertNth_apply_succAbove, Function.comp_apply, Equiv.trans_apply,
      finSuccEquiv'_succAbove, finSuccEquiv'_symm_some, Fin.succAbove_last]
    rfl

end FTQCLib.Frame.Walkthrough

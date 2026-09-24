/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Straightline
import ECCLib.GateChecker
import ECCLib.GaoField

set_option linter.unusedSectionVars false
set_option linter.style.show false

/-!
# The straightline adapters: CSE compilation, shared gate counts, and the two-level story

The thin layer joining the standalone SSA library (`Straightline.lean`) to the library's
gate stack:

* **The signature instances**: `boolInterp` reads the Boolean gate set (`not`, `and`,
  `xor`) into the SLP machinery; `Circuit.evalI` is the generic tree evaluation at ANY
  interpretation, agreeing with `Circuit.eval` at `boolInterp` and computing the tree's
  tropical depth at `depthInterp` — so ONE compiler induction, quantified over
  interpretations, yields value correctness and exact depth preservation together.
* **The CSE compiler** `compileC`: cache keys are RESOLVED rows (the emitted `Instr`,
  whose operands are already compiled references) — the design that makes one
  cache sound across outputs and stages. The cache IS the emitted line list: a lookup
  scans for an identical row, so soundness (`lines[k] = row`) and the exact-count
  `Nodup` come from the same construction with no separate invariant.
* **`compileC_spec` / `compileVecAux_spec`**: the one induction — prefix growth,
  well-formedness, `length ≤ size` (the tree count is an upper bound), output range,
  `Nodup` preservation, and `∀`-interpretation value agreement.
* **Program-level corollaries**: `compileProg_run` (semantics preserved),
  `compileProg_gates_le` (shared count ≤ tree count), `compileProg_nodup` (no duplicate
  rows — the sharing claim), `compileProg_depth` (CSE preserves depth EXACTLY).
* **The field level**: `FieldOps.interp` runs word-arithmetic programs on any computable
  carrier; a `FieldOps.Model` gives an `Interp.Hom` into the genuine field
  (`FieldOps.Model.interp_hom`), so `Interp.Hom.run_map` transports whole program runs —
  demonstrated at GF(16).
* **Witnesses**: the shared counts of the certified GF(16)/GF(256)
  multipliers, live evaluator rows, and the chain-vs-balanced depth separation.
-/

namespace ECCLib

open SLP

/-! ## The Boolean signature -/

/-- The unary op tag for Boolean circuits. -/
inductive BoolUn : Type where
  | bnot
  deriving DecidableEq, Repr

/-- The binary op tags for Boolean circuits. -/
inductive BoolBin : Type where
  | band
  | bxor
  deriving DecidableEq, Repr

/-- The Boolean interpretation of the circuit signature. -/
def boolInterp : Interp Bool BoolUn BoolBin Bool where
  cst := id
  un := fun _ b => !b
  bin := fun o a b => match o with
    | .band => a && b
    | .bxor => Bool.xor a b
  dflt := false

/-- Generic tree evaluation of a `Circuit` at ANY interpretation of the Boolean
signature. At `boolInterp` this is `Circuit.eval`; at `depthInterp` it is the tree's
gate depth. -/
def Circuit.evalI {V : Type*} (F : Interp Bool BoolUn BoolBin V) (x : Fin n → V) :
    Circuit n → V
  | .wire i => x i
  | .const b => F.cst b
  | .not c => F.un .bnot (Circuit.evalI F x c)
  | .and c d => F.bin .band (Circuit.evalI F x c) (Circuit.evalI F x d)
  | .xor c d => F.bin .bxor (Circuit.evalI F x c) (Circuit.evalI F x d)

theorem Circuit.evalI_boolInterp (x : Fin n → Bool) :
    ∀ c : Circuit n, Circuit.evalI boolInterp x c = c.eval x
  | .wire i => rfl
  | .const b => rfl
  | .not c => by
    rw [Circuit.evalI, Circuit.evalI_boolInterp x c]
    rfl
  | .and c d => by
    rw [Circuit.evalI, Circuit.evalI_boolInterp x c, Circuit.evalI_boolInterp x d]
    rfl
  | .xor c d => by
    rw [Circuit.evalI, Circuit.evalI_boolInterp x c, Circuit.evalI_boolInterp x d]
    rfl

/-- The tree's gate depth: the tropical reading of the generic evaluation, inputs at
depth 0. -/
def Circuit.depthT (c : Circuit n) : ℕ :=
  Circuit.evalI (depthInterp Bool BoolUn BoolBin) (fun _ => 0) c

/-! ## The row cache

The cache IS the emitted line list: looking a row up scans for an identical line. This
folds cache soundness (`lines[k] = row`) and key-uniqueness into one structure — a hit
returns an index whose line IS the row, and a miss appends, so the lines stay
duplicate-free by construction. -/

/-- First index of `a`, if present. -/
def lookupIdx {α : Type*} [DecidableEq α] (a : α) : List α → Option ℕ
  | [] => none
  | b :: l => if b = a then some 0 else (lookupIdx a l).map (· + 1)

theorem lookupIdx_eq_some {α : Type*} [DecidableEq α] {a : α} :
    ∀ {l : List α} {k : ℕ}, lookupIdx a l = some k →
      ∃ hk : k < l.length, l[k]'hk = a
  | [], k, h => by rw [lookupIdx] at h; exact absurd h (by simp)
  | b :: l, k, h => by
    rw [lookupIdx] at h
    by_cases hb : b = a
    · rw [if_pos hb] at h
      obtain rfl : (0 : ℕ) = k := Option.some.inj h
      exact ⟨Nat.succ_pos _, hb⟩
    · rw [if_neg hb] at h
      cases hh : lookupIdx a l with
      | none => rw [hh] at h; exact absurd h (by simp)
      | some k' =>
        rw [hh] at h
        simp only [Option.map_some] at h
        obtain rfl : k' + 1 = k := Option.some.inj h
        obtain ⟨hk', hl⟩ := lookupIdx_eq_some hh
        exact ⟨Nat.succ_lt_succ hk', hl⟩

theorem lookupIdx_eq_none {α : Type*} [DecidableEq α] {a : α} :
    ∀ {l : List α}, lookupIdx a l = none → a ∉ l
  | [], _ => by simp
  | b :: l, h => by
    rw [lookupIdx] at h
    by_cases hb : b = a
    · rw [if_pos hb] at h; exact absurd h (by simp)
    · rw [if_neg hb] at h
      have hnone : lookupIdx a l = none := by
        cases hh : lookupIdx a l with
        | none => rfl
        | some k' => rw [hh] at h; exact absurd h (by simp)
      intro hmem
      rcases List.mem_cons.1 hmem with heq | hmem'
      · exact hb heq.symm
      · exact lookupIdx_eq_none hnone hmem'

variable {C U B : Type*} [DecidableEq C] [DecidableEq U] [DecidableEq B]

/-- Emit a row with sharing: a cache hit returns the existing line's register, a miss
appends the row as a new line. -/
def emit (r : Instr C U B n) (L : List (Instr C U B n)) :
    Arg C n × List (Instr C U B n) :=
  match lookupIdx r L with
  | some k => (.reg k, L)
  | none => (.reg L.length, L ++ [r])

/-- The whole content of `emit`, in one statement: the lines grow by a prefix of at most
one row, stay well-formed and duplicate-free, and — for EVERY interpretation — the
returned operand resolves to the row's own step over the final environment. The hit case
is `getD_lineVals_at` (the fixpoint lemma) verbatim. -/
theorem emit_spec (r : Instr C U B n) (L : List (Instr C U B n))
    (hwf : wfb 0 L = true) (hok : r.okAt L.length = true) :
    L <+: (emit r L).2
    ∧ wfb 0 (emit r L).2 = true
    ∧ (emit r L).2.length ≤ L.length + 1
    ∧ ((emit r L).1.okAt (emit r L).2.length = true)
    ∧ (L.Nodup → (emit r L).2.Nodup)
    ∧ ∀ (V : Type) (F : Interp C U B V) (x : Fin n → V),
        (emit r L).1.resolve F x (lineVals F x (emit r L).2)
          = r.step F x (lineVals F x (emit r L).2) := by
  cases hlk : lookupIdx r L with
  | some k =>
    obtain ⟨hk, hLk⟩ := lookupIdx_eq_some hlk
    have hemit : emit r L = ((Arg.reg k, L) : Arg C n × List (Instr C U B n)) := by
      unfold emit
      rw [hlk]
    rw [hemit]
    refine ⟨List.prefix_refl _, hwf, Nat.le_succ _, ?_, id, ?_⟩
    · rw [Arg.okAt, decide_eq_true_iff]
      exact hk
    · intro V F x
      show (lineVals F x L).getD k F.dflt = r.step F x (lineVals F x L)
      rw [getD_lineVals_at F x hwf hk, hLk]
  | none =>
    have hnotmem : r ∉ L := lookupIdx_eq_none hlk
    have hemit : emit r L
        = ((Arg.reg L.length, L ++ [r]) : Arg C n × List (Instr C U B n)) := by
      unfold emit
      rw [hlk]
    have hwf' : wfb 0 (L ++ [r]) = true := by
      rw [wfb_append, Bool.and_eq_true]
      refine ⟨hwf, ?_⟩
      rw [Nat.zero_add, wfb, wfb, Bool.and_true]
      exact hok
    rw [hemit]
    refine ⟨List.prefix_append _ _, hwf', by simp, ?_, ?_, ?_⟩
    · rw [Arg.okAt, decide_eq_true_iff, List.length_append, List.length_singleton]
      omega
    · intro hnd
      rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton r, fun a ha b hb => ?_⟩
      intro heq
      exact hnotmem (by rwa [heq, List.mem_singleton.1 hb] at ha)
    · intro V F x
      have hj : L.length < (L ++ [r]).length := by
        rw [List.length_append, List.length_singleton]
        omega
      show (lineVals F x (L ++ [r])).getD L.length F.dflt
        = r.step F x (lineVals F x (L ++ [r]))
      rw [getD_lineVals_at F x hwf' hj]
      congr 1
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp

/-! ## The CSE compiler -/

/-- Compile a circuit tree into shared lines: leaves become operands directly (they cost
nothing, by the operands-carry-leaves design), and every gate row is emitted through the
cache. Plain `let` (not pattern-matching `let`) so the equations unfold by `rfl`. -/
def compileC : Circuit n → List (Instr Bool BoolUn BoolBin n) →
    Arg Bool n × List (Instr Bool BoolUn BoolBin n)
  | .wire i, L => (.inp i, L)
  | .const b, L => (.cst b, L)
  | .not c, L =>
    let p := compileC c L
    emit (.un .bnot p.1) p.2
  | .and c d, L =>
    let p := compileC c L
    let q := compileC d p.2
    emit (.bin .band p.1 q.1) q.2
  | .xor c d, L =>
    let p := compileC c L
    let q := compileC d p.2
    emit (.bin .bxor p.1 q.1) q.2

/-- **The one induction**: compiling preserves the accumulated lines as a prefix, keeps
them well-formed and duplicate-free, grows them by at most the tree's gate count, returns
an in-range operand — and, for EVERY interpretation at once, that operand resolves to the
tree's generic evaluation. Instantiating the last clause at `boolInterp` gives value
correctness; at `depthInterp` it gives exact depth preservation of CSE. -/
theorem compileC_spec : ∀ (c : Circuit n) (L : List (Instr Bool BoolUn BoolBin n)),
    wfb 0 L = true →
    L <+: (compileC c L).2
    ∧ wfb 0 (compileC c L).2 = true
    ∧ (compileC c L).2.length ≤ L.length + c.size
    ∧ ((compileC c L).1.okAt (compileC c L).2.length = true)
    ∧ (L.Nodup → (compileC c L).2.Nodup)
    ∧ ∀ (V : Type) (F : Interp Bool BoolUn BoolBin V) (x : Fin n → V),
        (compileC c L).1.resolve F x (lineVals F x (compileC c L).2)
          = Circuit.evalI F x c
  | .wire i, L, hwf =>
    ⟨List.prefix_refl _, hwf, Nat.le_refl _, rfl, id, fun V F x => rfl⟩
  | .const b, L, hwf =>
    ⟨List.prefix_refl _, hwf, Nat.le_refl _, rfl, id, fun V F x => rfl⟩
  | .not c, L, hwf => by
    obtain ⟨hpre₁, hwf₁, hlen₁, hok₁, hnd₁, hval₁⟩ := compileC_spec c L hwf
    have hokr : (Instr.un (B := BoolBin) BoolUn.bnot (compileC c L).1).okAt
        (compileC c L).2.length = true := hok₁
    obtain ⟨hpre₂, hwf₂, hlen₂, hok₂, hnd₂, hval₂⟩ :=
      emit_spec (Instr.un .bnot (compileC c L).1) (compileC c L).2 hwf₁ hokr
    have hunfold : compileC (.not c) L
        = emit (Instr.un .bnot (compileC c L).1) (compileC c L).2 := rfl
    rw [hunfold]
    refine ⟨hpre₁.trans hpre₂, hwf₂, ?_, hok₂, fun h => hnd₂ (hnd₁ h), ?_⟩
    · rw [Circuit.size_not]
      omega
    · intro V F x
      rw [hval₂ V F x]
      show F.un .bnot ((compileC c L).1.resolve F x
        (lineVals F x (emit (Instr.un .bnot (compileC c L).1) (compileC c L).2).2)) = _
      rw [Arg.resolve_prefix F x hpre₂ hok₁, hval₁ V F x]
      rfl
  | .and c d, L, hwf => by
    obtain ⟨hpre₁, hwf₁, hlen₁, hok₁, hnd₁, hval₁⟩ := compileC_spec c L hwf
    obtain ⟨hpre₂, hwf₂, hlen₂, hok₂, hnd₂, hval₂⟩ :=
      compileC_spec d (compileC c L).2 hwf₁
    have hok₁' : (compileC c L).1.okAt (compileC d (compileC c L).2).2.length = true :=
      Arg.okAt_mono hpre₂.length_le hok₁
    have hokr : (Instr.bin (U := BoolUn) BoolBin.band (compileC c L).1
        (compileC d (compileC c L).2).1).okAt
        (compileC d (compileC c L).2).2.length = true := by
      rw [Instr.okAt, Bool.and_eq_true]
      exact ⟨hok₁', hok₂⟩
    obtain ⟨hpre₃, hwf₃, hlen₃, hok₃, hnd₃, hval₃⟩ :=
      emit_spec (Instr.bin .band (compileC c L).1 (compileC d (compileC c L).2).1)
        (compileC d (compileC c L).2).2 hwf₂ hokr
    have hunfold : compileC (.and c d) L
        = emit (Instr.bin .band (compileC c L).1 (compileC d (compileC c L).2).1)
            (compileC d (compileC c L).2).2 := rfl
    rw [hunfold]
    refine ⟨(hpre₁.trans hpre₂).trans hpre₃, hwf₃, ?_, hok₃,
      fun h => hnd₃ (hnd₂ (hnd₁ h)), ?_⟩
    · rw [Circuit.size_and]
      omega
    · intro V F x
      rw [hval₃ V F x]
      show F.bin .band
        ((compileC c L).1.resolve F x (lineVals F x
          (emit (Instr.bin .band (compileC c L).1 (compileC d (compileC c L).2).1)
            (compileC d (compileC c L).2).2).2))
        ((compileC d (compileC c L).2).1.resolve F x (lineVals F x
          (emit (Instr.bin .band (compileC c L).1 (compileC d (compileC c L).2).1)
            (compileC d (compileC c L).2).2).2)) = _
      rw [Arg.resolve_prefix F x (hpre₂.trans hpre₃) hok₁,
        Arg.resolve_prefix F x hpre₃ hok₂, hval₁ V F x, hval₂ V F x]
      rfl
  | .xor c d, L, hwf => by
    obtain ⟨hpre₁, hwf₁, hlen₁, hok₁, hnd₁, hval₁⟩ := compileC_spec c L hwf
    obtain ⟨hpre₂, hwf₂, hlen₂, hok₂, hnd₂, hval₂⟩ :=
      compileC_spec d (compileC c L).2 hwf₁
    have hok₁' : (compileC c L).1.okAt (compileC d (compileC c L).2).2.length = true :=
      Arg.okAt_mono hpre₂.length_le hok₁
    have hokr : (Instr.bin (U := BoolUn) BoolBin.bxor (compileC c L).1
        (compileC d (compileC c L).2).1).okAt
        (compileC d (compileC c L).2).2.length = true := by
      rw [Instr.okAt, Bool.and_eq_true]
      exact ⟨hok₁', hok₂⟩
    obtain ⟨hpre₃, hwf₃, hlen₃, hok₃, hnd₃, hval₃⟩ :=
      emit_spec (Instr.bin .bxor (compileC c L).1 (compileC d (compileC c L).2).1)
        (compileC d (compileC c L).2).2 hwf₂ hokr
    have hunfold : compileC (.xor c d) L
        = emit (Instr.bin .bxor (compileC c L).1 (compileC d (compileC c L).2).1)
            (compileC d (compileC c L).2).2 := rfl
    rw [hunfold]
    refine ⟨(hpre₁.trans hpre₂).trans hpre₃, hwf₃, ?_, hok₃,
      fun h => hnd₃ (hnd₂ (hnd₁ h)), ?_⟩
    · rw [Circuit.size_xor]
      omega
    · intro V F x
      rw [hval₃ V F x]
      show F.bin .bxor
        ((compileC c L).1.resolve F x (lineVals F x
          (emit (Instr.bin .bxor (compileC c L).1 (compileC d (compileC c L).2).1)
            (compileC d (compileC c L).2).2).2))
        ((compileC d (compileC c L).2).1.resolve F x (lineVals F x
          (emit (Instr.bin .bxor (compileC c L).1 (compileC d (compileC c L).2).1)
            (compileC d (compileC c L).2).2).2)) = _
      rw [Arg.resolve_prefix F x (hpre₂.trans hpre₃) hok₁,
        Arg.resolve_prefix F x hpre₃ hok₂, hval₁ V F x, hval₂ V F x]
      rfl

/-! ## Whole netlists as programs -/

/-- Compile a list of output trees through ONE shared cache — cross-output sharing is
where the netlist counts drop (the measured 441 → 202 gap on the GF(256) multiplier). -/
def compileVecAux : List (Circuit n) → List (Instr Bool BoolUn BoolBin n) →
    List (Arg Bool n) × List (Instr Bool BoolUn BoolBin n)
  | [], L => ([], L)
  | c :: cs, L =>
    let p := compileC c L
    let q := compileVecAux cs p.2
    (p.1 :: q.1, q.2)

theorem compileVecAux_spec :
    ∀ (cs : List (Circuit n)) (L : List (Instr Bool BoolUn BoolBin n)),
    wfb 0 L = true →
    L <+: (compileVecAux cs L).2
    ∧ wfb 0 (compileVecAux cs L).2 = true
    ∧ (compileVecAux cs L).2.length ≤ L.length + (cs.map Circuit.size).sum
    ∧ (∀ a ∈ (compileVecAux cs L).1, a.okAt (compileVecAux cs L).2.length = true)
    ∧ (L.Nodup → (compileVecAux cs L).2.Nodup)
    ∧ ∀ (V : Type) (F : Interp Bool BoolUn BoolBin V) (x : Fin n → V),
        (compileVecAux cs L).1.map
            (fun a => a.resolve F x (lineVals F x (compileVecAux cs L).2))
          = cs.map (Circuit.evalI F x)
  | [], L, hwf => by
    refine ⟨List.prefix_refl _, hwf, Nat.le_refl _, ?_, id, fun V F x => rfl⟩
    intro a ha
    have ha' : a ∈ ([] : List (Arg Bool n)) := ha
    simp at ha'
  | c :: cs, L, hwf => by
    obtain ⟨hpre₁, hwf₁, hlen₁, hok₁, hnd₁, hval₁⟩ := compileC_spec c L hwf
    obtain ⟨hpre₂, hwf₂, hlen₂, hok₂, hnd₂, hval₂⟩ :=
      compileVecAux_spec cs (compileC c L).2 hwf₁
    have hunfold : compileVecAux (c :: cs) L
        = ((compileC c L).1 :: (compileVecAux cs (compileC c L).2).1,
           (compileVecAux cs (compileC c L).2).2) := rfl
    rw [hunfold]
    refine ⟨hpre₁.trans hpre₂, hwf₂, ?_, ?_, fun h => hnd₂ (hnd₁ h), ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      omega
    · intro a ha
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact Arg.okAt_mono hpre₂.length_le hok₁
      · exact hok₂ a ha'
    · intro V F x
      rw [List.map_cons, List.map_cons]
      congr 1
      · rw [Arg.resolve_prefix F x hpre₂ hok₁]
        exact hval₁ V F x
      · exact hval₂ V F x

/-- The compiled program of a netlist: shared lines from the empty cache, one output
operand per tree. -/
def compileProg (cs : List (Circuit n)) : Prog Bool BoolUn BoolBin n :=
  { lines := (compileVecAux cs []).2, outs := (compileVecAux cs []).1 }

theorem compileProg_WF (cs : List (Circuit n)) : (compileProg cs).WF := by
  obtain ⟨_, hwf, _, hok, _, _⟩ := compileVecAux_spec cs [] rfl
  exact ⟨hwf, by rw [List.all_eq_true]; exact hok⟩

/-- **Compiled semantics, at every interpretation at once**: the program's run is the
list of generic tree evaluations. -/
theorem compileProg_run (cs : List (Circuit n)) (V : Type)
    (F : Interp Bool BoolUn BoolBin V) (x : Fin n → V) :
    (compileProg cs).run F x = cs.map (Circuit.evalI F x) := by
  obtain ⟨_, _, _, _, _, hval⟩ := compileVecAux_spec cs [] rfl
  exact hval V F x

/-- Value correctness at the Boolean reading. -/
theorem compileProg_run_bool (cs : List (Circuit n)) (x : Fin n → Bool) :
    (compileProg cs).run boolInterp x = cs.map (fun c => c.eval x) := by
  rw [compileProg_run]
  exact List.map_congr_left fun c _ => Circuit.evalI_boolInterp x c

/-- **The shared count is bounded by the tree count**: compiled lines never exceed the
netlist's `size` sum. Strictness on real netlists is the measured sharing (105 → 37,
727 → 202). -/
theorem compileProg_gates_le (cs : List (Circuit n)) :
    (compileProg cs).lines.length ≤ (cs.map Circuit.size).sum := by
  obtain ⟨_, _, hlen, _, _, _⟩ := compileVecAux_spec cs [] rfl
  simpa using hlen

/-- **No duplicate rows**: no gate is counted twice. Together with `compileProg_gates_le`
this makes the compiled line count an exact count of distinct gates. -/
theorem compileProg_nodup (cs : List (Circuit n)) : (compileProg cs).lines.Nodup := by
  obtain ⟨_, _, _, _, hnd, _⟩ := compileVecAux_spec cs [] rfl
  exact hnd List.nodup_nil

/-- **CSE preserves depth EXACTLY**: the compiled program's depth is the max of the
trees' tropical depths — sharing rewires the DAG but never lengthens (or shortens) a
critical path. The proof is `compileProg_run` at `depthInterp`; no second induction. -/
theorem compileProg_depth (cs : List (Circuit n)) :
    (compileProg cs).depth = (cs.map Circuit.depthT).foldr max 0 := by
  rw [Prog.depth, compileProg_run]
  rfl

/-- Compile a `CircuitVec` netlist. -/
def compileNet (cv : Circuit.CircuitVec n m) : Prog Bool BoolUn BoolBin n :=
  compileProg (List.ofFn cv)

/-- The compiled netlist computes `evalVec` — the gate stack's semantic anchor. -/
theorem compileNet_run (cv : Circuit.CircuitVec n m) (x : Fin n → Bool) :
    (compileNet cv).run boolInterp x = List.ofFn (Circuit.evalVec cv x) := by
  rw [compileNet, compileProg_run_bool, List.map_ofFn]
  rfl

/-- The compiled netlist's shared count is bounded by `sizeVec`. -/
theorem compileNet_gates_le (cv : Circuit.CircuitVec n m) :
    (compileNet cv).lines.length ≤ Circuit.sizeVec cv := by
  refine (compileProg_gates_le _).trans ?_
  rw [List.map_ofFn, Circuit.sizeVec]
  rw [List.sum_ofFn]
  exact Nat.le_refl _

/-! ## The field-word level

The second consumer of the same SLP machinery: arithmetic circuits over field words.
`FieldOps.interp` runs a program on any computable carrier; a `FieldOps.Model` upgrades
to an `Interp.Hom`, so `run_map` transports whole runs into the genuine field — one
program text, two readings, demonstrated at GF(16). Lives in the `Coding` namespace with
`FieldOps` itself. -/

namespace Coding

/-- Unary op tags for field-word arithmetic. -/
inductive FUn : Type where
  | fneg
  | finv
  deriving DecidableEq, Repr

/-- Binary op tags for field-word arithmetic. -/
inductive FBin : Type where
  | fadd
  | fmul
  deriving DecidableEq, Repr

/-- Run field-word programs on any computable carrier: ops as data, constants inline,
junk default `zero`. -/
def FieldOps.interp {R : Type*} (ops : FieldOps R) : Interp R FUn FBin R where
  cst := id
  un := fun o v => match o with
    | .fneg => ops.neg v
    | .finv => ops.inv v
  bin := fun o v w => match o with
    | .fadd => ops.add v w
    | .fmul => ops.mul v w
  dflt := ops.zero

/-- The genuine-field interpretation, word constants embedded through `φ`. -/
def fieldInterp {R F : Type*} [Field F] (φ : R → F) : Interp R FUn FBin F where
  cst := φ
  un := fun o v => match o with
    | .fneg => -v
    | .finv => v⁻¹
  bin := fun o v w => match o with
    | .fadd => v + w
    | .fmul => v * w
  dflt := 0

/-- A `FieldOps.Model` is an interpretation homomorphism — the bridge that lets
`Interp.Hom.run_map` transport whole program runs from words to the field. -/
theorem FieldOps.Model.interp_hom {R F : Type*} [Field F] {ops : FieldOps R}
    {φ : R → F} (M : ops.Model φ) : Interp.Hom ops.interp (fieldInterp φ) φ where
  map_cst := fun _ => rfl
  map_un := fun o v => by
    cases o with
    | fneg => exact M.map_neg v
    | finv => exact M.map_inv v
  map_bin := fun o v w => by
    cases o with
    | fadd => exact M.map_add v w
    | fmul => exact M.map_mul v w
  map_dflt := M.map_zero

/-- **The two-level transport**: a word program's field reading IS the `φ`-image of its
word run — for the whole program at once. -/
theorem FieldOps.Model.run_interp {R F : Type*} [Field F] {ops : FieldOps R}
    {φ : R → F} (M : ops.Model φ) (P : Prog R FUn FBin n) (x : Fin n → R) :
    P.run (fieldInterp φ) (fun i => φ (x i)) = (P.run ops.interp x).map φ :=
  (M.interp_hom).run_map x P

/-- The one-gate word multiplier — a program text shared by every carrier. -/
def mulWordP {R : Type*} : Prog R FUn FBin 2 :=
  { lines := [.bin .fmul (.inp 0) (.inp 1)], outs := [.reg 0] }

theorem mulWordP_run {R : Type*} (ops : FieldOps R) (x : Fin 2 → R) :
    mulWordP.run ops.interp x = [ops.mul (x 0) (x 1)] := rfl

/-- The two-level story at GF(16): the SAME program text, run on certified words and —
through `gf16Model` — read in the genuine field `GF16p`. -/
theorem mulWordP_gf16 (x : Fin 2 → (Fin 4 → ZMod 2)) :
    mulWordP.run (fieldInterp (emb (m := 3) (AdjoinRoot.root (nu 3 r4p))))
        (fun i => emb (m := 3) (AdjoinRoot.root (nu 3 r4p)) (x i))
      = [emb (m := 3) (AdjoinRoot.root (nu 3 r4p)) (x 0)
          * emb (m := 3) (AdjoinRoot.root (nu 3 r4p)) (x 1)] := by
  rw [gf16Model.run_interp mulWordP x, mulWordP_run gf16Ops x, List.map_singleton,
    gf16Model.map_mul]

-- a live run through the shared text: α¹ · α⁴ = α⁵ on the certified GF(16) words
example : mulWordP.run gf16Ops.interp
    (fun i => if i = 0 then powVec r4p 1 else powVec r4p 4) = [powVec r4p 5] := by decide

end Coding

/-! ## Witnesses

**The shared multiplier counts** are interpreter measurements, not kernel theorems: kernel
`decide` of the compiles is infeasible (it did not finish in 200 s; the cache scan is
kernel-heavy), while `#eval` through List-materialized power tables (the Pi-form `tbl r8` is
exponentially slow in the interpreter) gives instantly:

* **GF(16)** (`cfoldVec (bilinNet (tbl r4))`, the certified 105-gate tree):
  **37 shared gates** (75 unfolded), compiled depth 5;
* **GF(256)** (`cfoldVec (bilinNet (tbl r8))`, the certified 727-gate tree):
  **202 shared gates** (441 unfolded), compiled depth 9.

What IS proved, for these nets among all others:
`compileNet_run` (the compiled program computes `evalVec` on every input),
`compileNet_gates_le` (shared count ≤ `sizeVec`), `compileProg_nodup` (no duplicate
rows), `compileProg_depth` (depth preserved exactly). The rows below witness the
machinery live at kernel-checkable scale. -/

section Witness

/-- The 8-input XOR chain: 7 lines at depth 7. -/
def chainXor8 : Prog Bool BoolUn BoolBin 8 :=
  { lines := [.bin .bxor (.inp 0) (.inp 1),
              .bin .bxor (.reg 0) (.inp 2),
              .bin .bxor (.reg 1) (.inp 3),
              .bin .bxor (.reg 2) (.inp 4),
              .bin .bxor (.reg 3) (.inp 5),
              .bin .bxor (.reg 4) (.inp 6),
              .bin .bxor (.reg 5) (.inp 7)],
    outs := [.reg 6] }

/-- The balanced 8-input XOR, built by `foldBalAux`: the same 7 lines, at depth
`3 = Nat.clog 2 8` — the depth theorem's non-vacuity, live. -/
def balXor8 : Prog Bool BoolUn BoolBin 8 :=
  { lines := (foldBalAux (U := BoolUn) BoolBin.bxor false 7 0
      (List.ofFn (fun i : Fin 8 => Arg.inp i))).1,
    outs := [(foldBalAux (U := BoolUn) BoolBin.bxor false 7 0
      (List.ofFn (fun i : Fin 8 => Arg.inp i))).2] }

-- the depth separation: same size, log vs linear depth (83/111/65 heartbeats)
example : chainXor8.depth = 7 := by decide
example : balXor8.depth = 3 := by decide
example : chainXor8.lines.length = 7 ∧ balXor8.lines.length = 7 := by decide

set_option maxRecDepth 4096 in
-- the two programs agree on ALL 256 inputs — the live evaluator row (33k heartbeats)
example : ∀ x : Fin 8 → Bool, chainXor8.run boolInterp x = balXor8.run boolInterp x := by
  decide

-- sharing, live: a duplicated output costs ZERO extra lines through the row cache
example : (compileProg [Circuit.dotC (fun _ : Fin 4 => (1 : ZMod 2)),
      Circuit.dotC (fun _ : Fin 4 => (1 : ZMod 2))]).lines.length
    = (compileProg [Circuit.dotC (fun _ : Fin 4 => (1 : ZMod 2))]).lines.length := by
  decide

-- the compiled linear form: 4 lines from the 4-gate tree (no sharing inside one `dotC`)
example : (compileProg [Circuit.dotC (fun _ : Fin 4 => (1 : ZMod 2))]).lines.length
    = 4 := by decide

end Witness

end ECCLib

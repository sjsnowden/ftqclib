/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.MinMax
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.style.show false

/-!
# Straightline programs over a parametrized signature

A small standalone library of **straightline programs** (SSA gate lists): the standard
representation on which circuit-complexity statements live, and — via hash-consing — the
canonical presentation of the free algebra *with sharing* (a duplicate-free,
topologically-sorted enumeration of term-DAG nodes).

Design:

* **Operands carry the leaves**: an `Arg` is an input wire, an inline constant, or a
  back-reference to an earlier line. Every `Instr` is therefore a genuine gate, so a
  program's **cost is its length, definitionally**.
* **Fixed arities 0/1/2 over three op-tag type parameters** `C U B` (constants, unary,
  binary). Instantiating at Booleans gives gate netlists; instantiating at a computable
  field-operations record gives arithmetic circuits over field words. Nothing here knows
  about either.
* **Extrinsic indices**: operand references are plain `ℕ` with a decidable Boolean
  well-formedness checker `wfb` (references point strictly backwards). Evaluation is
  total via a junk default (`Interp.dflt`); every *semantic* theorem carries a `wfb`
  hypothesis — junk-tolerance is for totality only.
* **One evaluator, many readings**: semantics is a single forward pass (`lineVals`);
  **depth is the same pass at the tropical interpretation** `(0, +1, max + 1)`.
  `Interp.Hom` transports runs along signature-respecting maps.
* `foldBal` builds **balanced** reductions (depth `≤ Nat.clog 2` of the width, against the
  linear chain), and `comp` composes programs with exact length accounting.

The load-bearing lemma is `getD_lineVals_at`: under well-formedness, each line's value is
its own instruction evaluated over the (stable) environment — the fixpoint reading that
makes hash-consing cache hits sound in one step.
-/

namespace ECCLib.SLP

/-! ## The syntax -/

/-- An operand: an input wire, an inline constant, or a reference to an earlier line.
Leaves live here, not in instructions — so instructions are exactly the gates. -/
inductive Arg (C : Type*) (n : ℕ) : Type _
  | inp (i : Fin n)
  | cst (c : C)
  | reg (k : ℕ)
  deriving DecidableEq, Repr

/-- One instruction: a unary or binary operation code applied to operands. Line `k` of a
program defines register `k`. -/
inductive Instr (C U B : Type*) (n : ℕ) : Type _
  | un (o : U) (a : Arg C n)
  | bin (o : B) (a b : Arg C n)
  deriving DecidableEq, Repr

/-- A denotation of the signature into values, as plain data (no typeclasses): constant,
unary, and binary denotations plus the junk default for out-of-range reads. -/
structure Interp (C U B V : Type*) where
  cst : C → V
  un : U → V → V
  bin : B → V → V → V
  dflt : V

/-- A straightline program: the gate list plus designated outputs. Cost is
`P.lines.length`, **by construction** — every line is a gate. -/
structure Prog (C U B : Type*) (n : ℕ) where
  lines : List (Instr C U B n)
  outs : List (Arg C n)
  deriving DecidableEq, Repr

variable {C U B V W : Type*} {n : ℕ}

/-! ## Evaluation -/

/-- Resolve an operand against the inputs and the environment of earlier line values. -/
def Arg.resolve (F : Interp C U B V) (x : Fin n → V) (env : List V) : Arg C n → V
  | .inp i => x i
  | .cst c => F.cst c
  | .reg k => env.getD k F.dflt

/-- One line's value from the environment of earlier line values. -/
def Instr.step (F : Interp C U B V) (x : Fin n → V) (env : List V) : Instr C U B n → V
  | .un o a => F.un o (a.resolve F x env)
  | .bin o a b => F.bin o (a.resolve F x env) (b.resolve F x env)

/-- The forward pass, from a given environment prefix. -/
def lineValsAux (F : Interp C U B V) (x : Fin n → V) :
    List V → List (Instr C U B n) → List V
  | env, [] => env
  | env, ins :: L => lineValsAux F x (env ++ [ins.step F x env]) L

/-- The values of all lines, in order. -/
def lineVals (F : Interp C U B V) (x : Fin n → V) (L : List (Instr C U B n)) : List V :=
  lineValsAux F x [] L

/-- The program's outputs. -/
def Prog.run (F : Interp C U B V) (x : Fin n → V) (P : Prog C U B n) : List V :=
  P.outs.map fun a => a.resolve F x (lineVals F x P.lines)

/-! ## The pass lemmas -/

theorem lineValsAux_append (F : Interp C U B V) (x : Fin n → V)
    (env : List V) (L M : List (Instr C U B n)) :
    lineValsAux F x env (L ++ M) = lineValsAux F x (lineValsAux F x env L) M := by
  induction L generalizing env with
  | nil => rfl
  | cons ins L ih => rw [List.cons_append, lineValsAux, lineValsAux, ih]

theorem lineValsAux_length (F : Interp C U B V) (x : Fin n → V) :
    ∀ (L : List (Instr C U B n)) (env : List V),
      (lineValsAux F x env L).length = env.length + L.length
  | [], env => by simp [lineValsAux]
  | ins :: L, env => by
    rw [lineValsAux, lineValsAux_length F x L]
    simp
    omega

theorem lineVals_length (F : Interp C U B V) (x : Fin n → V) (L : List (Instr C U B n)) :
    (lineVals F x L).length = L.length := by
  rw [lineVals, lineValsAux_length]
  simp

/-- The pass only appends: the starting environment is a prefix of the result. This is
prefix stability — emitting further lines never changes earlier values. -/
theorem prefix_lineValsAux (F : Interp C U B V) (x : Fin n → V) :
    ∀ (L : List (Instr C U B n)) (env : List V), env <+: lineValsAux F x env L
  | [], env => List.prefix_refl env
  | ins :: L, env => by
    rw [lineValsAux]
    exact List.IsPrefix.trans (List.prefix_append env _) (prefix_lineValsAux F x L _)

/-- Reads below a prefix's length agree with the prefix. -/
theorem IsPrefix.getD_eq {l₁ l₂ : List V} (h : l₁ <+: l₂) {k : ℕ} (hk : k < l₁.length)
    (d : V) : l₂.getD k d = l₁.getD k d := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hk]

/-! ## Well-formedness -/

/-- An operand is admissible at line position `j` when its register references point
strictly below `j`. -/
def Arg.okAt (j : ℕ) : Arg C n → Bool
  | .reg k => decide (k < j)
  | _ => true

def Instr.okAt (j : ℕ) : Instr C U B n → Bool
  | .un _ a => a.okAt j
  | .bin _ a b => a.okAt j && b.okAt j

/-- The well-formedness checker from a start position: decidable by construction,
subtraction-free. -/
def wfb : ℕ → List (Instr C U B n) → Bool
  | _, [] => true
  | j, ins :: L => ins.okAt j && wfb (j + 1) L

/-- Program well-formedness: backward-pointing lines, in-range outputs. -/
def Prog.WF (P : Prog C U B n) : Prop :=
  wfb 0 P.lines = true ∧ P.outs.all (Arg.okAt P.lines.length) = true

theorem Arg.okAt_mono {j j' : ℕ} (h : j ≤ j') {a : Arg C n} (ha : a.okAt j = true) :
    a.okAt j' = true := by
  cases a with
  | reg k =>
    rw [okAt, decide_eq_true_iff] at ha ⊢
    omega
  | inp i => rfl
  | cst c => rfl

theorem Instr.okAt_mono {j j' : ℕ} (h : j ≤ j') {ins : Instr C U B n}
    (hins : ins.okAt j = true) : ins.okAt j' = true := by
  cases ins with
  | un o a =>
    exact Arg.okAt_mono h hins
  | bin o a b =>
    rw [okAt, Bool.and_eq_true] at hins ⊢
    exact ⟨Arg.okAt_mono h hins.1, Arg.okAt_mono h hins.2⟩

theorem wfb_append (s : ℕ) (L M : List (Instr C U B n)) :
    wfb s (L ++ M) = (wfb s L && wfb (s + L.length) M) := by
  induction L generalizing s with
  | nil => simp [wfb]
  | cons ins L ih =>
    rw [List.cons_append, wfb, wfb, ih, Bool.and_assoc, List.length_cons]
    ring_nf

/-- The per-position projection of the checker. -/
theorem okAt_of_wfb : ∀ {L : List (Instr C U B n)} {s : ℕ}, wfb s L = true →
    ∀ (j : ℕ) (hj : j < L.length), (L[j]).okAt (s + j) = true := by
  intro L
  induction L with
  | nil => intro s _ j hj; exact absurd hj (by simp)
  | cons ins L ih =>
    intro s hwf j hj
    rw [wfb, Bool.and_eq_true] at hwf
    cases j with
    | zero => simpa using hwf.1
    | succ j =>
      have := ih hwf.2 j (by simpa using Nat.lt_of_succ_lt_succ hj)
      rw [show s + (j + 1) = s + 1 + j from by omega]
      simpa using this

/-! ## The fixpoint lemma -/

theorem Arg.resolve_congr (F : Interp C U B V) (x : Fin n → V) {env₁ env₂ : List V}
    {j : ℕ} {a : Arg C n} (ha : a.okAt j = true)
    (h : ∀ k, k < j → env₁.getD k F.dflt = env₂.getD k F.dflt) :
    a.resolve F x env₁ = a.resolve F x env₂ := by
  cases a with
  | inp i => rfl
  | cst c => rfl
  | reg k =>
    rw [okAt, decide_eq_true_iff] at ha
    exact h k ha

theorem Instr.step_congr (F : Interp C U B V) (x : Fin n → V) {env₁ env₂ : List V}
    {j : ℕ} {ins : Instr C U B n} (hins : ins.okAt j = true)
    (h : ∀ k, k < j → env₁.getD k F.dflt = env₂.getD k F.dflt) :
    ins.step F x env₁ = ins.step F x env₂ := by
  cases ins with
  | un o a =>
    rw [step, step, Arg.resolve_congr F x hins h]
  | bin o a b =>
    rw [okAt, Bool.and_eq_true] at hins
    rw [step, step, Arg.resolve_congr F x hins.1 h, Arg.resolve_congr F x hins.2 h]

/-- **The fixpoint lemma**: under well-formedness, each line's value is its own
instruction evaluated over the full environment (stable, since the instruction's operands
point strictly backwards). This is the single lemma a hash-consing cache hit consumes. -/
theorem getD_lineVals_at (F : Interp C U B V) (x : Fin n → V)
    {L : List (Instr C U B n)} (hwf : wfb 0 L = true) {j : ℕ} (hj : j < L.length) :
    (lineVals F x L).getD j F.dflt = Instr.step F x (lineVals F x L) L[j] := by
  -- decompose at j
  have hsplit : L.take (j + 1) ++ L.drop (j + 1) = L := List.take_append_drop _ _
  have htake : L.take (j + 1) = L.take j ++ [L[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]
    rfl
  have hlen_take : (L.take j).length = j := by
    rw [List.length_take]
    omega
  -- the value at j is set by the one-step extension of the take-j pass
  have hvals_take : lineVals F x (L.take (j + 1))
      = lineVals F x (L.take j) ++ [Instr.step F x (lineVals F x (L.take j)) L[j]] := by
    rw [htake, lineVals, lineValsAux_append]
    rfl
  have hlen_valsj : (lineVals F x (L.take j)).length = j := by
    rw [lineVals_length, hlen_take]
  -- prefix chain: lineVals (take j) <+: lineVals (take (j+1)) <+: lineVals L
  have hpre1 : lineVals F x (L.take (j + 1)) <+: lineVals F x L := by
    conv_rhs => rw [← hsplit, lineVals, lineValsAux_append]
    exact prefix_lineValsAux F x _ _
  have hpre0 : lineVals F x (L.take j) <+: lineVals F x L := by
    refine List.IsPrefix.trans ?_ hpre1
    rw [hvals_take]
    exact List.prefix_append _ _
  -- read the value at j through the prefixes
  have hread : (lineVals F x L).getD j F.dflt
      = Instr.step F x (lineVals F x (L.take j)) L[j] := by
    rw [IsPrefix.getD_eq hpre1 (by rw [lineVals_length, List.length_take]; omega),
      hvals_take, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      hlen_valsj]
    simp
  rw [hread]
  -- the step is stable from the take-j environment to the full one
  have hok : (L[j]).okAt j = true := by
    have := okAt_of_wfb hwf j hj
    simpa using this
  refine Instr.step_congr F x hok fun k hk => ?_
  exact (IsPrefix.getD_eq hpre0 (by omega) _).symm

/-- A prefix of the lines yields a prefix of the values. -/
theorem lineVals_prefix (F : Interp C U B V) (x : Fin n → V) {L L' : List (Instr C U B n)}
    (h : L <+: L') : lineVals F x L <+: lineVals F x L' := by
  obtain ⟨M, rfl⟩ := h
  rw [lineVals, lineVals, lineValsAux_append]
  exact prefix_lineValsAux F x _ _

/-- Operand resolution is stable under extending the program — the transport a compiler
uses to carry subterm values forward as it emits more lines. -/
theorem Arg.resolve_prefix (F : Interp C U B V) (x : Fin n → V)
    {L L' : List (Instr C U B n)} (h : L <+: L') {a : Arg C n}
    (ha : a.okAt L.length = true) :
    a.resolve F x (lineVals F x L') = a.resolve F x (lineVals F x L) := by
  refine Arg.resolve_congr F x ha fun k hk => ?_
  refine IsPrefix.getD_eq (lineVals_prefix F x h) ?_ _
  rw [lineVals_length]
  exact hk

/-! ## Depth: the tropical reading -/

/-- The tropical interpretation: constants at depth 0, a unary gate adds one, a binary
gate adds one over the max. Running the SAME evaluator at this interpretation computes
longest paths — levelization, with no graph theory. -/
def depthInterp (C U B : Type*) : Interp C U B ℕ where
  cst _ := 0
  un _ d := d + 1
  bin _ d e := max d e + 1
  dflt := 0

/-- The depth of a program (inputs at depth 0): the max over its outputs of the tropical
run. -/
def Prog.depth (P : Prog C U B n) : ℕ :=
  (P.run (depthInterp C U B) (fun _ => 0)).foldr max 0

/-! ## Transport along signature homomorphisms -/

/-- A map of value carriers respecting the two interpretations. `FieldOps.Model`-style
records provide instances; this is the weaker, forward-only transport structure. -/
structure Interp.Hom (F : Interp C U B V) (G : Interp C U B W) (φ : V → W) : Prop where
  map_cst : ∀ c, φ (F.cst c) = G.cst c
  map_un : ∀ o v, φ (F.un o v) = G.un o (φ v)
  map_bin : ∀ o v w, φ (F.bin o v w) = G.bin o (φ v) (φ w)
  map_dflt : φ F.dflt = G.dflt

theorem Interp.Hom.map_resolve {F : Interp C U B V} {G : Interp C U B W} {φ : V → W}
    (h : Interp.Hom F G φ) (x : Fin n → V) (env : List V) (a : Arg C n) :
    φ (a.resolve F x env) = a.resolve G (fun i => φ (x i)) (env.map φ) := by
  cases a with
  | inp i => rfl
  | cst c => exact h.map_cst c
  | reg k =>
    show φ (env.getD k F.dflt) = (env.map φ).getD k G.dflt
    rw [← h.map_dflt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases henv : env[k]? <;> simp

theorem Interp.Hom.map_step {F : Interp C U B V} {G : Interp C U B W} {φ : V → W}
    (h : Interp.Hom F G φ) (x : Fin n → V) (env : List V) (ins : Instr C U B n) :
    φ (ins.step F x env) = ins.step G (fun i => φ (x i)) (env.map φ) := by
  cases ins with
  | un o a => rw [Instr.step, Instr.step, h.map_un, h.map_resolve]
  | bin o a b => rw [Instr.step, Instr.step, h.map_bin, h.map_resolve, h.map_resolve]

theorem Interp.Hom.map_lineValsAux {F : Interp C U B V} {G : Interp C U B W} {φ : V → W}
    (h : Interp.Hom F G φ) (x : Fin n → V) :
    ∀ (L : List (Instr C U B n)) (env : List V),
      lineValsAux G (fun i => φ (x i)) (env.map φ) L = (lineValsAux F x env L).map φ
  | [], env => rfl
  | ins :: L, env => by
    rw [lineValsAux, lineValsAux, ← Interp.Hom.map_lineValsAux h x L]
    congr 1
    rw [List.map_append, List.map_singleton, h.map_step]

/-- **Transport**: one program text, two value carriers — the run commutes with any
signature homomorphism. -/
theorem Interp.Hom.run_map {F : Interp C U B V} {G : Interp C U B W} {φ : V → W}
    (h : Interp.Hom F G φ) (x : Fin n → V) (P : Prog C U B n) :
    P.run G (fun i => φ (x i)) = (P.run F x).map φ := by
  rw [Prog.run, Prog.run, List.map_map]
  refine List.map_congr_left fun a _ => ?_
  rw [Function.comp_apply]
  have hl : lineVals G (fun i => φ (x i)) P.lines = (lineVals F x P.lines).map φ := by
    rw [lineVals, lineVals, ← Interp.Hom.map_lineValsAux h x P.lines []]
    rfl
  rw [hl, ← h.map_resolve]

/-! ## The balanced fold

A pairwise-halving reduction of the inputs, built as a standalone program (reduction of
computed operands composes through `comp`). Depth is `Nat.clog 2` of the width — against
the linear chain's width-many levels — which is what makes a `depth` measure non-vacuous.
The neutral is a CONSTANT tag `z : C`, so its value is environment-free. -/

/-- One pairwise pass at the value level. -/
def pairPassV (op : V → V → V) : List V → List V
  | a :: b :: rest => op a b :: pairPassV op rest
  | l => l

/-- One pairwise pass at the syntax level: adjacent operand pairs become new lines
(numbered consecutively from `base`); a leftover operand passes through. -/
def pairPass (o : B) (base : ℕ) : List (Arg C n) → List (Instr C U B n) × List (Arg C n)
  | a :: b :: rest =>
      let r := pairPass o (base + 1) rest
      (.bin o a b :: r.1, .reg base :: r.2)
  | l => ([], l)

theorem pairPassV_length (op : V → V → V) : ∀ l : List V,
    (pairPassV op l).length = (l.length + 1) / 2
  | [] => by simp [pairPassV]
  | [a] => by simp [pairPassV]
  | a :: b :: rest => by
    rw [pairPassV, List.length_cons, pairPassV_length op rest]
    simp only [List.length_cons]
    omega

theorem pairPass_snd_map_resolve (F : Interp C U B V) (x : Fin n → V) (o : B) :
    ∀ (args : List (Arg C n)) (env : List V),
      (∀ a ∈ args, a.okAt env.length = true) →
      wfb env.length (pairPass (U := U) o env.length args).1 = true
      ∧ (∀ a ∈ (pairPass (U := U) o env.length args).2,
          a.okAt (env.length + (pairPass (U := U) o env.length args).1.length) = true)
      ∧ (pairPass (U := U) o env.length args).2.map
          (Arg.resolve F x (lineValsAux F x env (pairPass (U := U) o env.length args).1))
        = pairPassV (F.bin o) (args.map (Arg.resolve F x env))
  | [], env, _ => by
    exact ⟨rfl, by simp [pairPass], rfl⟩
  | [a], env, hok => by
    refine ⟨rfl, ?_, rfl⟩
    intro a' ha'
    have hpp : (pairPass (U := U) o env.length [a])
        = (([] : List (Instr C U B n)), [a]) := rfl
    rw [hpp] at ha'
    simp only [List.mem_singleton] at ha'
    subst ha'
    rw [hpp]
    exact Arg.okAt_mono (Nat.le_add_right _ _) (hok a' (List.mem_singleton.mpr rfl))
  | a :: b :: rest, env, hok => by
    -- the new line and the extended environment
    have hoka : a.okAt env.length = true := hok a (by simp)
    have hokb : b.okAt env.length = true := hok b (by simp)
    set v : V := Instr.step F x env (.bin o a b) with hv
    set env' : List V := env ++ [v] with henv'
    have hlen' : env'.length = env.length + 1 := by
      rw [henv', List.length_append, List.length_singleton]
    have hokrest : ∀ a' ∈ rest, a'.okAt env'.length = true := fun a' ha' =>
      Arg.okAt_mono (by omega) (hok a' (by simp [ha']))
    obtain ⟨ihwf, ihok, ihvals⟩ := pairPass_snd_map_resolve F x o rest env' hokrest
    rw [hlen'] at ihwf ihok ihvals
    -- unfold one pass step
    have hpp : pairPass (U := U) o env.length (a :: b :: rest)
        = ((.bin o a b :: (pairPass (U := U) o (env.length + 1) rest).1,
            .reg env.length :: (pairPass (U := U) o (env.length + 1) rest).2)
           : List (Instr C U B n) × List (Arg C n)) := rfl
    rw [hpp]
    have hvals_lines : lineValsAux F x env
        (Instr.bin o a b :: (pairPass (U := U) o (env.length + 1) rest).1)
        = lineValsAux F x env' (pairPass (U := U) o (env.length + 1) rest).1 := by
      rw [lineValsAux, henv']
    refine ⟨?_, ?_, ?_⟩
    · -- well-formedness of the emitted lines
      rw [wfb, Bool.and_eq_true]
      exact ⟨by rw [Instr.okAt, Bool.and_eq_true]; exact ⟨hoka, hokb⟩, ihwf⟩
    · -- next-round operands in range
      intro a' ha'
      simp only [List.length_cons, List.mem_cons] at ha' ⊢
      rcases ha' with rfl | ha'
      · rw [Arg.okAt, decide_eq_true_iff]
        omega
      · have := ihok a' ha'
        refine Arg.okAt_mono (by omega) this
    · -- value tracking
      rw [List.map_cons, List.map_cons, List.map_cons, pairPassV, hvals_lines]
      congr 1
      · -- the head: the new register reads the new line's value
        have hpre : env' <+: lineValsAux F x env' (pairPass (U := U) o (env.length + 1) rest).1 :=
          prefix_lineValsAux F x _ _
        show (lineValsAux F x env' (pairPass (U := U) o (env.length + 1) rest).1).getD
            env.length F.dflt
          = F.bin o (a.resolve F x env) (b.resolve F x env)
        rw [IsPrefix.getD_eq hpre (by omega) _]
        rw [henv', List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp [hv, Instr.step]
      · have hrest_env : rest.map (Arg.resolve F x env') = rest.map (Arg.resolve F x env) := by
          refine List.map_congr_left fun a' ha' => ?_
          refine Arg.resolve_congr F x (hok a' (by simp [ha'])) fun k hk => ?_
          rw [henv']
          exact IsPrefix.getD_eq (List.prefix_append env [v]) hk _
        rw [← hrest_env]
        exact ihvals

/-- The pure fact: one pairwise pass preserves the (associative) fold. -/
theorem foldr_pairPassV (op : V → V → V) (hassoc : Std.Associative op) (e : V) :
    ∀ l : List V, (pairPassV op l).foldr op e = l.foldr op e
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => by
    rw [pairPassV, List.foldr_cons, List.foldr_cons, List.foldr_cons,
      foldr_pairPassV op hassoc e rest, hassoc.assoc]

/-- The balanced-fold builder on fuel: rounds of pairwise passes until one operand
remains. -/
def foldBalAux (o : B) (z : C) : ℕ → ℕ → List (Arg C n) → List (Instr C U B n) × Arg C n
  | 0, _, args => ([], args.headD (.cst z))
  | _ + 1, _, [] => ([], .cst z)
  | _ + 1, _, [a] => ([], a)
  | fuel + 1, base, a :: b :: rest =>
      let r := pairPass o base (a :: b :: rest)
      let s := foldBalAux o z fuel (base + r.1.length) r.2
      (r.1 ++ s.1, s.2)

/-- **The balanced fold's value**, under associativity and a right-neutral constant: the
emitted lines are well-formed, the result operand is in range, and it computes the fold of
the operands' values. -/
theorem foldBalAux_spec (F : Interp C U B V) (x : Fin n → V) (o : B) (z : C)
    (hassoc : Std.Associative (F.bin o)) (hneut : ∀ v, F.bin o v (F.cst z) = v) :
    ∀ (fuel : ℕ) (args : List (Arg C n)) (env : List V),
      (∀ a ∈ args, a.okAt env.length = true) → args.length ≤ fuel + 1 →
      wfb env.length (foldBalAux (U := U) o z fuel env.length args).1 = true
      ∧ (foldBalAux (U := U) o z fuel env.length args).2.okAt
          (env.length + (foldBalAux (U := U) o z fuel env.length args).1.length) = true
      ∧ (foldBalAux (U := U) o z fuel env.length args).2.resolve F x
            (lineValsAux F x env (foldBalAux (U := U) o z fuel env.length args).1)
        = (args.map (Arg.resolve F x env)).foldr (F.bin o) (F.cst z) := by
  intro fuel
  induction fuel with
  | zero =>
    intro args env hok hlen
    match args with
    | [] => exact ⟨rfl, rfl, rfl⟩
    | [a] =>
      refine ⟨rfl, Arg.okAt_mono (Nat.le_add_right _ _) (hok a (by simp)), ?_⟩
      show a.resolve F x env = F.bin o (a.resolve F x env) (F.cst z)
      rw [hneut]
  | succ fuel ih =>
    intro args env hok hlen
    match args with
    | [] => exact ⟨rfl, rfl, rfl⟩
    | [a] =>
      refine ⟨rfl, Arg.okAt_mono (Nat.le_add_right _ _) (hok a (by simp)), ?_⟩
      show a.resolve F x env = F.bin o (a.resolve F x env) (F.cst z)
      rw [hneut]
    | a :: b :: rest =>
      obtain ⟨hwf₁, hok₁, hvals₁⟩ := pairPass_snd_map_resolve F x o (a :: b :: rest) env hok
      set r := pairPass o env.length (a :: b :: rest) with hr
      set env₁ : List V := lineValsAux F x env r.1 with henv₁
      have hlen₁ : env₁.length = env.length + r.1.length := by
        rw [henv₁, lineValsAux_length]
      have hlen_r2 : r.2.length ≤ fuel + 1 := by
        have h1 : r.2.length = ((a :: b :: rest).length + 1) / 2 := by
          have := congrArg List.length hvals₁
          rw [List.length_map, pairPassV_length, List.length_map] at this
          exact this
        simp only [List.length_cons] at h1 hlen
        omega
      obtain ⟨ihwf, ihok, ihvals⟩ := ih r.2 env₁ (by rw [hlen₁]; exact hok₁) hlen_r2
      rw [hlen₁] at ihwf ihok ihvals
      have hunfold : foldBalAux o z (fuel + 1) env.length (a :: b :: rest)
          = (r.1 ++ (foldBalAux o z fuel (env.length + r.1.length) r.2).1,
             (foldBalAux o z fuel (env.length + r.1.length) r.2).2) := rfl
      rw [hunfold]
      have hvals_app : lineValsAux F x env
          (r.1 ++ (foldBalAux o z fuel (env.length + r.1.length) r.2).1)
          = lineValsAux F x env₁ (foldBalAux o z fuel (env.length + r.1.length) r.2).1 := by
        rw [lineValsAux_append, henv₁]
      refine ⟨?_, ?_, ?_⟩
      · rw [wfb_append, Bool.and_eq_true]
        exact ⟨hwf₁, ihwf⟩
      · rw [List.length_append]
        have := ihok
        refine Arg.okAt_mono (by omega) this
      · rw [hvals_app, ihvals, hvals₁, foldr_pairPassV (F.bin o) hassoc]

theorem pairPass_fst_length (o : B) : ∀ (base : ℕ) (args : List (Arg C n)),
    (pairPass (U := U) o base args).1.length = args.length / 2
  | _, [] => by simp [pairPass]
  | _, [a] => by simp [pairPass]
  | base, a :: b :: rest => by
    have h := pairPass_fst_length o (base + 1) rest
    show ((Instr.bin o a b :: (pairPass (U := U) o (base + 1) rest).1
      : List (Instr C U B n))).length = _
    rw [List.length_cons, h]
    simp only [List.length_cons]
    omega

theorem pairPass_snd_length (o : B) : ∀ (base : ℕ) (args : List (Arg C n)),
    (pairPass (U := U) o base args).2.length = (args.length + 1) / 2
  | _, [] => by simp [pairPass]
  | _, [a] => by simp [pairPass]
  | base, a :: b :: rest => by
    have h := pairPass_snd_length o (base + 1) rest
    show ((Arg.reg base :: (pairPass (U := U) o (base + 1) rest).2 : List (Arg C n))).length = _
    rw [List.length_cons, h]
    simp only [List.length_cons]
    omega

/-- The balanced fold's exact size, subtraction-free: on a nonempty operand list it emits
one line fewer than the width. -/
theorem foldBalAux_fst_length (o : B) (z : C) :
    ∀ (fuel base : ℕ) (args : List (Arg C n)), args.length ≤ fuel + 1 → args ≠ [] →
      (foldBalAux (U := U) o z fuel base args).1.length + 1 = args.length
  | 0, base, args, hlen, hne => by
    match args, hne with
    | [a], _ => rfl
    | a :: b :: rest, _ =>
      exfalso
      simp only [List.length_cons] at hlen
      omega
    | [], hne => exact absurd rfl hne
  | fuel + 1, base, args, hlen, hne => by
    match args, hne with
    | [], hne => exact absurd rfl hne
    | [a], _ => rfl
    | a :: b :: rest, _ =>
      have h1 := pairPass_fst_length (U := U) o base (a :: b :: rest)
      have h2 := pairPass_snd_length (U := U) o base (a :: b :: rest)
      have hr2ne : (pairPass (U := U) o base (a :: b :: rest)).2 ≠ [] := by
        intro h
        have hl := congrArg List.length h
        rw [h2] at hl
        simp only [List.length_cons, List.length_nil] at hl
        omega
      have hr2len : (pairPass (U := U) o base (a :: b :: rest)).2.length ≤ fuel + 1 := by
        rw [h2]
        simp only [List.length_cons] at hlen ⊢
        omega
      have ih := foldBalAux_fst_length o z fuel
        (base + (pairPass (U := U) o base (a :: b :: rest)).1.length)
        (pairPass (U := U) o base (a :: b :: rest)).2 hr2len hr2ne
      show ((pairPass (U := U) o base (a :: b :: rest)).1
        ++ (foldBalAux (U := U) o z fuel
            (base + (pairPass (U := U) o base (a :: b :: rest)).1.length)
            (pairPass (U := U) o base (a :: b :: rest)).2).1).length + 1 = _
      rw [List.length_append, h1]
      rw [h1, h2] at ih
      simp only [List.length_cons] at *
      omega

/-! ## Composition -/

/-- Substitute a program's operands: inputs through `ρ`, registers shifted past the host's
lines. -/
def Arg.subst (ρ : Fin m → Arg C n) (s : ℕ) : Arg C m → Arg C n
  | .inp i => ρ i
  | .cst c => .cst c
  | .reg k => .reg (k + s)

def Instr.subst (ρ : Fin m → Arg C n) (s : ℕ) : Instr C U B m → Instr C U B n
  | .un o a => .un o (a.subst ρ s)
  | .bin o a b => .bin o (a.subst ρ s) (b.subst ρ s)

/-- **Composition**: `P`'s outputs feed `Q`'s inputs; `Q`'s registers shift past `P`'s
lines. Length is EXACTLY additive (`comp_lines_length`) — sharing across the seam is the
compiler's job, not composition's. -/
def comp (P : Prog C U B n) {m : ℕ} (Q : Prog C U B m) (h : P.outs.length = m) :
    Prog C U B n :=
  { lines := P.lines ++ Q.lines.map
      (Instr.subst (fun i => P.outs[(i : ℕ)]'(by rw [h]; exact i.isLt)) P.lines.length)
    outs := Q.outs.map
      (Arg.subst (fun i => P.outs[(i : ℕ)]'(by rw [h]; exact i.isLt)) P.lines.length) }

theorem comp_lines_length (P : Prog C U B n) {m : ℕ} (Q : Prog C U B m)
    (h : P.outs.length = m) :
    (comp P Q h).lines.length = P.lines.length + Q.lines.length := by
  simp [comp]

/-- Substituted operands resolve on the concatenated environment as the original operands
on the guest environment, with the host outputs as inputs. -/
theorem Arg.subst_resolve (F : Interp C U B V) (x : Fin n → V) {m : ℕ}
    {ρ : Fin m → Arg C n} {envP envQ : List V}
    (hρ : ∀ i, (ρ i).okAt envP.length = true)
    {a : Arg C m} (ha : a.okAt envQ.length = true) :
    (a.subst ρ envP.length).resolve F x (envP ++ envQ)
      = a.resolve F (fun i => (ρ i).resolve F x envP) envQ := by
  cases a with
  | inp i =>
    show (ρ i).resolve F x (envP ++ envQ) = (ρ i).resolve F x envP
    refine Arg.resolve_congr F x (hρ i) fun k hk => ?_
    exact IsPrefix.getD_eq (List.prefix_append envP envQ) hk _
  | cst c => rfl
  | reg k =>
    show (envP ++ envQ).getD (k + envP.length) F.dflt = envQ.getD k F.dflt
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega),
      show k + envP.length - envP.length = k from by omega]

theorem Instr.subst_step (F : Interp C U B V) (x : Fin n → V) {m : ℕ}
    {ρ : Fin m → Arg C n} {envP envQ : List V}
    (hρ : ∀ i, (ρ i).okAt envP.length = true)
    {ins : Instr C U B m} (hins : ins.okAt envQ.length = true) :
    (ins.subst ρ envP.length).step F x (envP ++ envQ)
      = ins.step F (fun i => (ρ i).resolve F x envP) envQ := by
  cases ins with
  | un o a =>
    rw [subst, Instr.step, Instr.step, Arg.subst_resolve F x hρ hins]
  | bin o a b =>
    rw [Instr.okAt, Bool.and_eq_true] at hins
    rw [subst, Instr.step, Instr.step, Arg.subst_resolve F x hρ hins.1,
      Arg.subst_resolve F x hρ hins.2]

theorem lineValsAux_subst (F : Interp C U B V) (x : Fin n → V) {m : ℕ}
    {ρ : Fin m → Arg C n} {envP : List V} (hρ : ∀ i, (ρ i).okAt envP.length = true) :
    ∀ (QL : List (Instr C U B m)) (envQ : List V), wfb envQ.length QL = true →
      lineValsAux F x (envP ++ envQ) (QL.map (Instr.subst ρ envP.length))
        = envP ++ lineValsAux F (fun i => (ρ i).resolve F x envP) envQ QL
  | [], envQ, _ => rfl
  | ins :: QL, envQ, hwf => by
    rw [wfb, Bool.and_eq_true] at hwf
    rw [List.map_cons, lineValsAux, lineValsAux,
      Instr.subst_step F x hρ hwf.1,
      show (envP ++ envQ) ++ [Instr.step F (fun i => (ρ i).resolve F x envP) envQ ins]
        = envP ++ (envQ ++ [Instr.step F (fun i => (ρ i).resolve F x envP) envQ ins])
        from (List.append_assoc _ _ _)]
    rw [← lineValsAux_subst F x hρ QL
      (envQ ++ [Instr.step F (fun i => (ρ i).resolve F x envP) envQ ins])
      (by rw [List.length_append, List.length_singleton]; exact hwf.2)]

/-- **Compositionality**: running the composite is running the guest on the host's
outputs. -/
theorem comp_run (F : Interp C U B V) (x : Fin n → V) {P : Prog C U B n} {m : ℕ}
    {Q : Prog C U B m} (h : P.outs.length = m)
    (hP : P.WF) (hQ : Q.WF) :
    (comp P Q h).run F x
      = Q.run F (fun i =>
          (P.outs[(i : ℕ)]'(by rw [h]; exact i.isLt)).resolve F x (lineVals F x P.lines)) := by
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨hQ1, hQ2⟩ := hQ
  rw [List.all_eq_true] at hP2 hQ2
  set ρ : Fin m → Arg C n := fun i => P.outs[(i : ℕ)]'(by rw [h]; exact i.isLt) with hρ_def
  have hρ : ∀ i, (ρ i).okAt (lineVals F x P.lines).length = true := by
    intro i
    rw [lineVals_length]
    exact hP2 _ (List.getElem_mem _)
  have hlines : lineVals F x ((comp P Q h).lines)
      = lineVals F x P.lines
        ++ lineVals F (fun i => (ρ i).resolve F x (lineVals F x P.lines)) Q.lines := by
    show lineValsAux F x [] (P.lines ++ Q.lines.map (Instr.subst ρ P.lines.length)) = _
    rw [lineValsAux_append]
    have hs : P.lines.length = (lineVals F x P.lines).length := (lineVals_length F x _).symm
    rw [show (lineValsAux F x [] P.lines) = lineVals F x P.lines from rfl]
    calc lineValsAux F x (lineVals F x P.lines) (Q.lines.map (Instr.subst ρ P.lines.length))
        = lineValsAux F x ((lineVals F x P.lines) ++ [])
            (Q.lines.map (Instr.subst ρ (lineVals F x P.lines).length)) := by
          rw [List.append_nil, ← hs]
      _ = (lineVals F x P.lines)
            ++ lineValsAux F (fun i => (ρ i).resolve F x (lineVals F x P.lines)) [] Q.lines := by
          exact lineValsAux_subst F x hρ Q.lines [] (by simpa using hQ1)
      _ = _ := rfl
  rw [Prog.run, Prog.run]
  show (Q.outs.map (Arg.subst ρ P.lines.length)).map
      (fun a => a.resolve F x (lineVals F x ((comp P Q h).lines))) = _
  rw [List.map_map]
  refine List.map_congr_left fun a ha => ?_
  rw [Function.comp_apply, hlines]
  have hs : P.lines.length = (lineVals F x P.lines).length := (lineVals_length F x _).symm
  rw [hs]
  refine Arg.subst_resolve F x hρ ?_
  rw [lineVals_length]
  exact hQ2 a ha

theorem Arg.subst_okAt {m : ℕ} {ρ : Fin m → Arg C n} {s : ℕ}
    (hρ : ∀ i, (ρ i).okAt s = true) {a : Arg C m} {k : ℕ} (ha : a.okAt k = true) :
    (a.subst ρ s).okAt (s + k) = true := by
  cases a with
  | inp i => exact okAt_mono (Nat.le_add_right s k) (hρ i)
  | cst c => rfl
  | reg j =>
    rw [okAt, decide_eq_true_iff] at ha
    show (Arg.reg (j + s)).okAt (s + k) = true
    rw [okAt, decide_eq_true_iff]
    omega

theorem Instr.subst_okAt {m : ℕ} {ρ : Fin m → Arg C n} {s : ℕ}
    (hρ : ∀ i, (ρ i).okAt s = true) {ins : Instr C U B m} {k : ℕ}
    (hins : ins.okAt k = true) : (ins.subst ρ s).okAt (s + k) = true := by
  cases ins with
  | un o a => exact Arg.subst_okAt hρ hins
  | bin o a b =>
    rw [okAt, Bool.and_eq_true] at hins
    rw [subst, okAt, Bool.and_eq_true]
    exact ⟨Arg.subst_okAt hρ hins.1, Arg.subst_okAt hρ hins.2⟩

theorem wfb_subst {m : ℕ} {ρ : Fin m → Arg C n} {s : ℕ}
    (hρ : ∀ i, (ρ i).okAt s = true) :
    ∀ (QL : List (Instr C U B m)) (k : ℕ), wfb k QL = true →
      wfb (s + k) (QL.map (Instr.subst ρ s)) = true
  | [], _, _ => rfl
  | ins :: QL, k, hwf => by
    rw [wfb, Bool.and_eq_true] at hwf
    rw [List.map_cons, wfb, Bool.and_eq_true]
    refine ⟨Instr.subst_okAt hρ hwf.1, ?_⟩
    have := wfb_subst hρ QL (k + 1) hwf.2
    rwa [← Nat.add_assoc] at this

/-- Composition preserves well-formedness — so composites feed `comp_run` again. -/
theorem comp_WF {P : Prog C U B n} {m : ℕ} {Q : Prog C U B m} (h : P.outs.length = m)
    (hP : P.WF) (hQ : Q.WF) : (comp P Q h).WF := by
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨hQ1, hQ2⟩ := hQ
  rw [List.all_eq_true] at hP2 hQ2
  set ρ : Fin m → Arg C n := fun i => P.outs[(i : ℕ)]'(by rw [h]; exact i.isLt) with hρ_def
  have hρ : ∀ i, (ρ i).okAt P.lines.length = true := fun i => hP2 _ (List.getElem_mem _)
  have hlines : (comp P Q h).lines
      = P.lines ++ Q.lines.map (Instr.subst ρ P.lines.length) := rfl
  have houts : (comp P Q h).outs = Q.outs.map (Arg.subst ρ P.lines.length) := rfl
  refine ⟨?_, ?_⟩
  · rw [hlines, wfb_append, Bool.and_eq_true]
    refine ⟨hP1, ?_⟩
    have hs := wfb_subst hρ Q.lines 0 hQ1
    rw [Nat.add_zero] at hs
    rwa [Nat.zero_add]
  · rw [List.all_eq_true]
    intro a ha
    rw [houts] at ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    have hk := Arg.subst_okAt hρ (hQ2 b hb)
    rw [comp_lines_length]
    exact hk

/-! ## The balanced fold's depth

`foldBalAux_spec` cannot see depth: the tropical `bin` is not associative. The bound comes
from re-running the SAME pass-tracking lemma (`pairPass_snd_map_resolve`, which needs no
associativity) at `depthInterp`: each pairwise round adds one level, and `Nat.clog 2`
rounds suffice. -/

/-- The pure fact: one tropical pairwise pass raises a uniform bound by at most one. -/
theorem pairPassV_depth_le {o : B} {M : ℕ} :
    ∀ {l : List ℕ}, (∀ v ∈ l, v ≤ M) →
      ∀ v ∈ pairPassV ((depthInterp C U B).bin o) l, v ≤ M + 1
  | [], _ => by simp [pairPassV]
  | [a], h => by
    intro v hv
    simp only [pairPassV, List.mem_singleton] at hv
    subst hv
    exact (h v (by simp)).trans (Nat.le_succ M)
  | a :: b :: rest, h => by
    intro v hv
    rw [pairPassV] at hv
    rcases List.mem_cons.1 hv with rfl | hv'
    · have ha := h a (by simp)
      have hb := h b (by simp)
      show max a b + 1 ≤ M + 1
      omega
    · exact pairPassV_depth_le (fun v' hv'' => h v' (by simp [hv''])) v hv'

/-- **The balanced fold's depth, in rounds**: if every operand resolves to depth `≤ M` and
the width fits in `2 ^ d`, the folded output resolves to depth `≤ M + d`. -/
theorem foldBalAux_depth_le (o : B) (z : C) (x : Fin n → ℕ) :
    ∀ (d M fuel : ℕ) (args : List (Arg C n)) (env : List ℕ),
      (∀ a ∈ args, a.okAt env.length = true) →
      args.length ≤ fuel + 1 → args.length ≤ 2 ^ d →
      (∀ a ∈ args, a.resolve (depthInterp C U B) x env ≤ M) →
      (foldBalAux (U := U) o z fuel env.length args).2.resolve (depthInterp C U B) x
          (lineValsAux (depthInterp C U B) x env
            (foldBalAux (U := U) o z fuel env.length args).1)
        ≤ M + d := by
  intro d
  induction d with
  | zero =>
    intro M fuel args env hok hfuel hpow hM
    match fuel, args with
    | 0, [] => exact Nat.zero_le _
    | 0, [a] => exact hM a (by simp)
    | fuel + 1, [] => exact Nat.zero_le _
    | fuel + 1, [a] => exact hM a (by simp)
    | _, a :: b :: rest =>
      exfalso
      simp only [List.length_cons, pow_zero] at hpow
      omega
  | succ d ih =>
    intro M fuel args env hok hfuel hpow hM
    match fuel, args with
    | 0, [] => exact Nat.zero_le _
    | 0, [a] => exact (hM a (by simp)).trans (Nat.le_add_right M (d + 1))
    | fuel + 1, [] => exact Nat.zero_le _
    | fuel + 1, [a] => exact (hM a (by simp)).trans (Nat.le_add_right M (d + 1))
    | 0, a :: b :: rest =>
      exfalso
      simp only [List.length_cons] at hfuel
      omega
    | fuel + 1, a :: b :: rest =>
      obtain ⟨hwf₁, hok₁, hvals₁⟩ :=
        pairPass_snd_map_resolve (depthInterp C U B) x o (a :: b :: rest) env hok
      set r := pairPass (U := U) o env.length (a :: b :: rest) with hr
      set env₁ : List ℕ := lineValsAux (depthInterp C U B) x env r.1 with henv₁
      have hlen₁ : env₁.length = env.length + r.1.length := by
        rw [henv₁, lineValsAux_length]
      have hlen_r2 : r.2.length = ((a :: b :: rest).length + 1) / 2 :=
        pairPass_snd_length (U := U) o env.length (a :: b :: rest)
      have hfuel₂ : r.2.length ≤ fuel + 1 := by
        simp only [List.length_cons] at hlen_r2 hfuel
        omega
      have hpow₂ : r.2.length ≤ 2 ^ d := by
        have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
        simp only [List.length_cons] at hlen_r2 hpow
        omega
      have hM₂ : ∀ a' ∈ r.2, a'.resolve (depthInterp C U B) x env₁ ≤ M + 1 := by
        intro a' ha'
        have hmem : a'.resolve (depthInterp C U B) x env₁
            ∈ pairPassV ((depthInterp C U B).bin o)
                ((a :: b :: rest).map (Arg.resolve (depthInterp C U B) x env)) := by
          rw [← hvals₁]
          exact List.mem_map.2 ⟨a', ha', rfl⟩
        refine pairPassV_depth_le (fun v hv => ?_) _ hmem
        obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 hv
        exact hM a₀ ha₀
      have ih' := ih (M + 1) fuel r.2 env₁ (by rw [hlen₁]; exact hok₁) hfuel₂ hpow₂ hM₂
      rw [hlen₁] at ih'
      have hunfold : foldBalAux (U := U) o z (fuel + 1) env.length (a :: b :: rest)
          = (r.1 ++ (foldBalAux (U := U) o z fuel (env.length + r.1.length) r.2).1,
             (foldBalAux (U := U) o z fuel (env.length + r.1.length) r.2).2) := rfl
      rw [hunfold]
      have hvals_app : lineValsAux (depthInterp C U B) x env
          (r.1 ++ (foldBalAux (U := U) o z fuel (env.length + r.1.length) r.2).1)
          = lineValsAux (depthInterp C U B) x env₁
              (foldBalAux (U := U) o z fuel (env.length + r.1.length) r.2).1 := by
        rw [lineValsAux_append, henv₁]
      rw [hvals_app]
      exact le_trans ih' (by omega)

/-- **The balanced fold's depth**: `Nat.clog 2` of the width over the operand bound — the
statement that makes the `depth` measure non-vacuous (a linear chain costs width-many
levels). -/
theorem foldBalAux_depth_le_clog (o : B) (z : C) (x : Fin n → ℕ) (M : ℕ)
    (fuel : ℕ) (args : List (Arg C n)) (env : List ℕ)
    (hok : ∀ a ∈ args, a.okAt env.length = true)
    (hfuel : args.length ≤ fuel + 1)
    (hM : ∀ a ∈ args, a.resolve (depthInterp C U B) x env ≤ M) :
    (foldBalAux (U := U) o z fuel env.length args).2.resolve (depthInterp C U B) x
        (lineValsAux (depthInterp C U B) x env
          (foldBalAux (U := U) o z fuel env.length args).1)
      ≤ M + Nat.clog 2 args.length :=
  foldBalAux_depth_le o z x _ M fuel args env hok hfuel
    (Nat.le_pow_clog one_lt_two _) hM

end ECCLib.SLP
